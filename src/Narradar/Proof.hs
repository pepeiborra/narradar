{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude, PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Proof where

import Control.Applicative
import qualified Control.Monad as M
import "monad-param" Control.Monad.Parameterized as MonadP
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), toList, sum)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Data.Traversable as T hiding (mapM)
import Text.XHtml (Html)

import qualified Language.Prolog.Syntax as Prolog (Program)
import qualified TRS.Types as TRS

import Narradar.Types hiding (Ppr(..),ppr, (!))
import qualified Narradar.Types as TRS
import Narradar.Utils
import qualified Narradar.ArgumentFiltering as AF

import Control.Monad.Free

import Prelude hiding (sum, log, mapM, foldr, concatMap, Monad(..), (=<<))
import qualified Prelude as P
-- ---------
-- Proofs
-- ---------

data ProofF s k =
    And     {procInfo::SomeInfo, problem::SomeProblem, subProblems::[k]}
  | Or      {procInfo::SomeInfo, problem::SomeProblem, subProblems::[k]}
  | Step    {procInfo::SomeInfo, problem::SomeProblem, subProblem::k}
  | Success {procInfo::SomeInfo, problem::SomeProblem, res::s}
  | Fail    {procInfo::SomeInfo, problem::SomeProblem, res::s}
  | DontKnow{procInfo::SomeInfo, problem::SomeProblem}
  | MPlus k k
  | MZero

type Proof s a            = Free (ProofF s) a
type ProblemProof     s f = Proof s (Problem f)
type ProblemProofG id s f = Proof s (ProblemG id f)

success  pi p0 s = Impure (Success (someInfo pi) (someProblem p0) s)
success' pi p0 s = Impure (Success pi p0 s)
failP    pi p0 s = Impure (Fail (someInfo pi) (someProblem p0) s)
choiceP  p1 p2   = Impure (MPlus p1 p2)
dontKnow pi p0   = Impure (DontKnow (someInfo pi) (someProblem p0))
andP pi p0 []    = success pi p0 mempty
andP pi p0 pp    = Impure (And (someInfo pi) (someProblem p0) pp)
andP' pi p0 []   = success' pi p0 mempty
andP' pi p0 pp   = Impure (And pi p0 pp)
orP  pi p0 []    = success pi p0 mempty
orP  pi p0 pp    = Impure (Or (someInfo pi) (someProblem p0) pp)
orP' pi p0 []    = success' pi p0 mempty
orP' pi p0 pp    = Impure (Or pi p0 pp)
step pi p0 p     = Impure (Step (someInfo pi) (someProblem p0) (returnM p))

htmlProof :: ProblemProofG id Html f -> ProblemProofG id Html f
htmlProof = id

deriving instance (Show s, Show k) => Show (ProofF s k)

data SomeProblem where
    SomeProblem       :: (Show id, TRS.Ppr f) => ProblemG id f -> SomeProblem
--    SomePrologProblem :: [Goal] -> Prolog.Program -> SomeProblem

instance Show SomeProblem where
    show (SomeProblem p) = "<some problem>"
--    show (SomePrologProblem gg pgm) = show (PrologProblem Prolog gg pgm :: Problem BasicId)

someProblem :: (Show id, TRS.Ppr f) => ProblemG id f -> SomeProblem
someProblem p@Problem{}      = SomeProblem p
--someProblem (PrologProblem typ gg pgm) = SomePrologProblem gg pgm


data SomeInfo where SomeInfo :: Show id => ProcInfo id -> SomeInfo
instance Show SomeInfo where show (SomeInfo pi) = show pi

someInfo = SomeInfo
-- -----------------
-- Functor instances
-- -----------------
instance Foldable (ProofF s) where foldMap = foldMapDefault
$(derive makeFunctor     ''ProofF)
$(derive makeTraversable ''ProofF)

-- -------------------
-- MonadPlus instances
-- -------------------

instance MonadZero (Free (ProofF s)) where mzeroM = Impure MZero
instance MPlus (Free (ProofF s)) (Free (ProofF s)) (Free (ProofF s))  where
    p1 `mplus` p2 = if isSuccess p1 then p1 else choiceP p1 p2


-- ------------------
-- Monad Transformer
-- ------------------
-- we are going to need a monad transformer (for the Aprove proc)

type ProofT   s m a = FreeT (ProofF s) m a
type PPT id f s m   = ProofT s m (ProblemG id f)

liftProofT :: P.Monad m => Proof s a -> ProofT s m a
liftProofT = wrap

{-
instance Monad m => MPlus (FreeT (ProofF f s) m) (FreeT (ProofF f s) m) (FreeT (ProofF f s) m) where
    p1 `mplus` p2 = FreeT $ go $ do
                      s1  <- runProofT p1
                      if isSuccess s1 then unFreeT(wrap s1)
                         else do s2  <- runProofT p2
                                 unFreeT (wrap(choiceP s1 s2))
-}

instance P.Monad m => MonadZero (FreeT (ProofF s) m) where mzeroM = wrap(Impure MZero)
instance Monad m => MPlus (FreeT (ProofF s) m) (FreeT (ProofF s) m) (FreeT (ProofF s) m) where
    mplus m1 m2 = FreeT $ returnM $ Right (MPlus m1 m2)

-- ----------
-- Evaluator
-- ----------
--runProofT x = unwrap x

runProofT :: (Monoid s) => ProofT s IO a -> IO (Proof s a)
runProofT m = go (unFreeT m >>= f) where
  f (Left v)  = returnM (returnM v)
  f (Right p) = eval p
--  eval :: ProofF f s (ProofT f s m a) -> m (Proof f s a)
  -- Special cases
  eval (And pi pb pp) = tryAll pp >>= return . andP' pi pb
--  eval (And pi pb pp) = (parMapM 4 runProofT pp >>= return . andP pi pb) -- run in parallel speculatively
  eval (MPlus p1 p2)  = do
    s1 <- runProofT p1
    if isSuccess s1 then returnM s1
     else do
       s2 <- runProofT p2
       return (choiceP s1 s2)
  eval (Or pi pb pp)  = (tryAny pp >>= return . orP' pi pb)
  -- For all the rest, just unwrap
  eval x = Impure <$> mapMP runProofT x
  -- Desist on failure
  tryAll [] = returnM []
  tryAll (x:xs) = do
    s <- runProofT x
    if not(isSuccess s) then returnM [s] else (s:) <$> tryAll xs
  -- Stop on success
  tryAny [] = returnM []
  tryAny (x:xs) = do
    s <- runProofT x
    if isSuccess s then returnM [s] else (s:) <$> tryAny xs

-- ------------------
-- Algebra of proofs
-- ------------------
isSuccessF :: ProofF s Bool -> Bool
isSuccessF Fail{}         = False
isSuccessF Success{}      = True
isSuccessF DontKnow{}     = False
isSuccessF (And _ _ ll)   = and ll
isSuccessF (Or  _ _ [])   = True  -- unstandard
isSuccessF (Or  _ _ ll)   = or ll
isSuccessF MZero          = False
isSuccessF (MPlus p1 p2)  = p1 || p2
isSuccessF (Step _ _ p)   = p

isSuccess :: Proof s k -> Bool
isSuccess  = foldFree  (const False) isSuccessF

isSuccessT = foldFreeT (const $ returnM False) (returnM.isSuccessF)

simplify :: Monoid s => ProblemProofG id s f -> ProblemProofG id s f
simplify = foldFree returnM simplifyF where

simplifyF = f where
  f   (Or  pi p [])  = success' pi p mempty -- "No additional problems left"
  f p@(Or  _ _ aa)   = msum aa
  f   (And p f [])   = error "simplify: empty And clause (probably a bug in your code)"
  f p@(MPlus p1 p2)
      | isSuccess p1 = p1
      | isSuccess p2 = p2
      | otherwise    = mzeroM
  f p                = Impure p


logLegacy proc prob Nothing    = failP proc prob "Failed"
logLegacy proc prob (Just msg) = success proc prob msg