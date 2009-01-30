{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude, PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Proof where

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

import Types hiding (Ppr(..),ppr, (!))
import qualified Types as TRS
import qualified TRS.Types as TRS
import Utils
import TaskPoolSTM
import qualified ArgumentFiltering as AF

import Control.Monad.Free

import Prelude as P hiding (sum, log, mapM, foldr, concatMap, Monad(..), (=<<))

-- ---------
-- Proofs
-- ---------

data ProofF f (s :: *) k =
    And     {procInfo::ProcInfo, problem::Problem f, subProblems::[k]}
  | Or      {procInfo::ProcInfo, problem::Problem f, subProblems::[k]}
  | Step    {procInfo::ProcInfo, problem::Problem f, subProblem::k}
  | Success {procInfo::ProcInfo, problem::Problem f, res::s}
  | Fail    {procInfo::ProcInfo, problem::Problem f, res::s}
  | DontKnow{procInfo::ProcInfo, problem::Problem f}
  | MPlus k k
  | MZero
     deriving (Show)

type Proof f s a      = Free (ProofF f s) a
type ProblemProof s f = Proof f s (Problem f)

success = ((Impure.).) . Success
failP   = ((Impure.).) . Fail
choiceP = (Impure.)    . MPlus
dontKnow= (Impure.)    . DontKnow
andP pi p0 [] = success pi p0 mempty
andP pi p0 pp = Impure (And pi p0 pp)
orP  pi p0 [] = success pi p0 mempty
orP  pi p0 pp = Impure (Or pi p0 pp)
step pi p0 p  = Impure (Step pi p0 (returnM p))

-- -----------------
-- Functor instances
-- -----------------
instance Foldable (ProofF f s) where foldMap = foldMapDefault
$(derive makeFunctor     ''ProofF)
$(derive makeTraversable ''ProofF)

-- -------------------
-- MonadPlus instances
-- -------------------

instance MonadZero (Free (ProofF f s)) where mzeroM = Impure MZero
instance MPlus (Free (ProofF f s)) (Free (ProofF f s)) (Free (ProofF f s))  where
    p1 `mplus` p2 = if isSuccess p1 then p1 else choiceP p1 p2


-- ------------------
-- Monad Transformer
-- ------------------
-- we are going to need a monad transformer (for the Aprove proc)

type ProofT f s m a = FreeT (ProofF f s) m a
type PPT      s m f = ProofT f s m (Problem f)

liftProofT :: Monad m => Proof f s a -> ProofT f s m a
liftProofT = wrap

{-
instance Monad m => MPlus (FreeT (ProofF f s) m) (FreeT (ProofF f s) m) (FreeT (ProofF f s) m) where
    p1 `mplus` p2 = FreeT $ go $ do
                      s1  <- runProofT p1
                      if isSuccess s1 then unFreeT(wrap s1)
                         else do s2  <- runProofT p2
                                 unFreeT (wrap(choiceP s1 s2))
-}

instance Monad m => MPlus (FreeT (ProofF f s) m) (FreeT (ProofF f s) m) (FreeT (ProofF f s) m) where
    mplus m1 m2 = FreeT $ returnM $ Right (MPlus m1 m2)

-- ----------
-- Evaluator
-- ----------
--runProofT x = unwrap x

runProofT :: (Monoid s, Traversable f) => ProofT f s IO a -> IO (Proof f s a)
runProofT m = go (unFreeT m >>= f) where
  f (Left v)  = returnM (returnM v)
  f (Right p) = eval p
--  eval :: ProofF f s (ProofT f s m a) -> m (Proof f s a)
  -- Special cases
  eval (And pi pb pp) = tryAll pp >>= return . andP pi pb
--  eval (And pi pb pp) = (parMapM 4 runProofT pp >>= return . andP pi pb) -- run in parallel speculatively
  eval (MPlus p1 p2)  = do
    s1 <- runProofT p1
    if isSuccess s1 then returnM s1
     else do
       s2 <- runProofT p2
       return (choiceP s1 s2)
  eval (Or pi pb pp)  = (tryAny pp >>= return . orP pi pb)
  -- For all the rest, just unwrap
  eval x = Impure <$> mapMP unwrap x
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
isSuccessF :: ProofF f s Bool -> Bool
isSuccessF Fail{}         = False
isSuccessF Success{}      = True
isSuccessF DontKnow{}     = False
isSuccessF (And _ _ ll)   = and ll
isSuccessF (Or  _ _ [])   = True  -- unstandard
isSuccessF (Or  _ _ ll)   = or ll
isSuccessF MZero          = False
isSuccessF (MPlus p1 p2)  = p1 || p2
isSuccessF (Step _ _ p)   = p

isSuccess :: Proof f s k -> Bool
isSuccess  = foldFree  (const False) isSuccessF

isSuccessT = foldFreeT (const $ returnM False) (returnM.isSuccessF)

simplify :: Monoid s => ProblemProof s f -> ProblemProof s f
simplify = foldFree returnM f where
  f   (Or  pi p [])  = success pi p mempty -- "No additional problems left"
  f p@(Or  _ _ aa)   = msum aa
  f   (And p f [])   = error "simplify: empty And clause (probably a bug in your code)"
  f p@(MPlus p1 p2)
      | isSuccess p1 = p1
      | isSuccess p2 = p2
      | otherwise    = mzeroM
  f p                = Impure p


logLegacy proc prob Nothing    = failP proc prob "Failed"
logLegacy proc prob (Just msg) = success proc prob msg
