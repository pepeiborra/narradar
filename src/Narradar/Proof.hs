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
  | MAnd  k k
  | MDone

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
step' pi p0 p    = Impure (Step pi p0 p)
mand p1 p2       = Impure (MAnd p1 p2)
mdone            = Impure MDone
mall             = foldr mand mdone

htmlProof :: ProblemProofG id Html f -> ProblemProofG id Html f
htmlProof = id

deriving instance (Show s, Show k) => Show (ProofF s k)

data SomeProblem where
    SomeProblem       :: (TRSC f, T id :<: f, Ord id, Show id) => ProblemG id f -> SomeProblem
--    SomePrologProblem :: [Goal] -> Prolog.Program -> SomeProblem

instance Show SomeProblem where
    show (SomeProblem p) = "<some problem>"
--    show (SomePrologProblem gg pgm) = show (PrologProblem Prolog gg pgm :: Problem BasicId)

someProblem :: (TRSC f, T id :<: f, Ord id, Show id) => ProblemG id f -> SomeProblem
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

-- Additional parameterized instances between the Proof and ProofT
instance (P.Monad m, Monad m) => MPlus (Free (ProofF s)) (FreeT (ProofF s) m) (FreeT (ProofF s) m) where
    mplus m1 m2 = FreeT $ returnM $ Right (MPlus (wrap m1) m2)

instance (P.Monad m, Monad m) => MPlus (FreeT (ProofF s) m) (Free (ProofF s)) (FreeT (ProofF s) m) where
    mplus m1 m2 = FreeT $ returnM $ Right (MPlus  m1 (wrap m2))

-- ------------
-- * Evaluators
-- ------------

type Gen f = f -> f

-- | Prunes the proof tree in an unsafe way
--   Cannot be used to inspect an unfinished proof
--   since it will corrupt it
runAndPruneProofT :: (Monoid s) => ProofT s IO a -> IO (Proof s a)
runAndPruneProofT m = unFreeT m >>= f where
  f (Left v)  = returnM (returnM v)
  f (Right p) = eval' p
  eval' (And pi pb pp) = tryAll runAndPruneProofT pp >>= (return . andP' pi pb)
--  eval' (And pi pb pp) = (parMapM 4 runAndPruneProofT pp >>= return . andP' pi pb) -- run in parallel speculatively
  eval' x = eval runAndPruneProofT x

-- | Alternative version which only applies safe prunes.
--   A proof can be always be run unpruned with @Control.Monad.Free.unwrap@
runProofT :: (Monoid s) => ProofT s IO a -> IO (Proof s a)
runProofT m = unFreeT m >>= f where
  f (Left v)  = returnM (returnM v)
  f (Right p) = eval runProofT p


eval rec (MPlus p1 p2)  = do
    s1 <- rec p1
    if isSuccess s1 then returnM s1
     else do
       s2 <- rec p2
       return (choiceP s1 s2)
eval rec (Or pi pb pp) = tryAny rec pp >>= return . orP' pi pb
eval rec (MAnd p1 p2)  = rec p1 >>= \s1 -> if not(isSuccess s1) then returnM s1 else mand s1 <$> rec p2

 -- For all the rest, just unwrap
eval rec x = Impure <$> mapMP rec x

  -- Desist on failure
tryAll f [] = returnM []
tryAll f (x:xs) = do
    s <- f x
--    if isSuccess s then (s:) <$> tryAll xs else returnM [s, mzeroM] -- throw in a mzero "just to sleep better"
    if isSuccess s then (s:) <$> tryAll f xs else returnM [s]

  -- Stop on success
tryAny f [] = returnM []
tryAny f (x:xs) = do
    s <- f x
    if isSuccess s then returnM [s] else (s:) <$> tryAny f xs

-- ------------------
-- Algebra of proofs
-- ------------------
isSuccessF :: ProofF s Bool -> Bool
isSuccessF Fail{}         = False
isSuccessF Success{}      = True
isSuccessF DontKnow{}     = False
isSuccessF (And _ _ ll)   = and ll
isSuccessF (Or  _ _ [])   = True  -- HEADS UP unstandard
isSuccessF (Or  _ _ ll)   = or ll
isSuccessF (MPlus p1 p2)  = p1 || p2
isSuccessF MZero          = False
isSuccessF (MAnd  p1 p2)  = p1 && p2
isSuccessF MDone          = True
isSuccessF (Step _ _ p)   = p

isSuccess :: Proof s k -> Bool
isSuccess  = foldFree  (const False) isSuccessF

isSuccessT = foldFreeT (const $ returnM False) (returnM.isSuccessF)

simplify :: Monoid s => ProblemProofG id s f -> ProblemProofG id s f
simplify = foldFree returnM simplifyF where

simplifyF = f where
  f   (Or  pi p [])  = success' pi p mempty -- "No additional problems left"
  f   (Or  pi p aa)  = step' pi p (msum aa) -- (filter isSuccess aa)
  f   (And p f [])   = error "simplify: empty And clause (probably a bug in your code)"
  f p@(MPlus p1 p2)
      | isSuccess p1 = p1
      | isSuccess p2 = p2
      | otherwise    = mzeroM
  f p                = Impure p


logLegacy proc prob Nothing    = failP proc prob "Failed"
logLegacy proc prob (Just msg) = success proc prob msg
