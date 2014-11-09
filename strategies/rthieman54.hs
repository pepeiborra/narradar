{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}

-- module IPL14 where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Free
import Data.List (nub)
import Data.Maybe
import Data.Foldable as F
import Data.Traversable (Traversable)
import Data.Typeable
import qualified Data.Set as Set
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar hiding (lfp)
import Narradar.Processor.RPO
import Narradar.Processor.RPO.Yices
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Framework.GraphViz
import Lattice ()
import Narradar.Utils (pprTrace)
import Text.Printf

import Debug.Hoed.Observe

import Data.IORef
import System.IO.Unsafe

#ifndef WEB
import Narradar.Interface.Cli
main = do
  runO $ narradarMain listToMaybe
  lpos <- readIORef lpoCounter
  let lpoUnique = length (nub lpos)
  printf "Counted %d calls to lpo, %d unique" (length lpos) lpoUnique
#else
import Narradar.Interface.Cgi
main = narradarCgi listToMaybe
#endif


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("This version of Narradar does not handle problems of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "This version of Narradar does not support the input problem."

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = apply RewritingToQRewriting >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem IRewriting Id) where
  dispatch p = apply RewritingToQRewriting p >>= dispatch

-- Rewriting
instance () => Dispatch (NProblem (QRewritingN Id) Id) where
  dispatch = ev
             >=> lfp dgi >=> inst >=> dg >=> try ur >=> rew >=> dg >=> sc >=> dg
             >=> final
    where
      dgi = inn `orElse` ur `orElse` dg
      inn    = apply ToInnermost
      innO p = gdmobservers "Innermost" applyO ToInnermost p

instance (Pretty (DPIdentifier a), FrameworkId a
         ) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = ev >=> rpoPlus gt1 >=> final

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch = ev >=> rpoPlus gt1 >=> final
{-
instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = apply RewritingToQRewriting >=> dispatch

instance Dispatch (NProblem (InitialGoal (TermF Id) (QRewritingN Id)) Id) where
  dispatch = ev >=> ( inn .|.
                      (rpoPlus gt2 >=> final))
-}
-- Relative
instance Dispatch (NProblem (Relative (NTRS Id) (InitialGoal (TermF Id) Rewriting)) Id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

instance (Dispatch (NProblem base id)
         ,FrameworkProblemN base id
         ,PprTPDB (NProblem base id)
         ,Ord(NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

-- Solvers
dg_ = DependencyGraphSCC{useInverse=True}
dg = apply dg_
sc = apply SubtermCriterion
dgsc = lfp(dg >=> sc)
ev = apply ExtraVarsP
inn = apply ToInnermost >=> dispatch
ur    = apply UsableRules
narr = apply (NarrowingP Nothing)
narrP p x = apply (NarrowingP (Just p)) x
inst  = apply Instantiation
rew   = apply RewritingP
finst = apply FInstantiation
scO p = gdmobservers "Subterm criterion" applyO SubtermCriterion p
urO p = gdmobservers "Usable Rules" applyO UsableRules p
instO p = gdmobservers "Instantiation" applyO Instantiation p
rewO p = gdmobservers "Rewriting" applyO RewritingP p
narrO p = gdmobservers "Narrowing" applyO (NarrowingP (Just p))
dgO p = gdmobservers "Graph" applyO (DependencyGraphSCC False) p

rpoPlus transform
   = repeatSolver 2 (dgsc >=> (lpo .|. rpos .|. transform))

lpoCounter :: IORef [Doc]
lpoCounter = unsafePerformIO $ do
  c <- newIORef []
  return c

lpo = lpoO' nilObserver
lpoO = gdmobservers "LPO" lpoO'
lpoO' o p  = unsafePerformIO$ do
  modifyIORef lpoCounter $ (pPrint p :)
  return $ applyO o (RPOProc LPOAF  Needed SMTFFI True) p
mpo  = apply (RPOProc MPOAF  Needed SMTFFI True)
lpos = apply (RPOProc LPOSAF Needed SMTFFI True)
rpo  = apply (RPOProc RPOAF  Needed SMTFFI True)
rpos = apply (RPOProc RPOSAF Needed SMTFFI True)

gt1 = apply RewritingP .||. narr .||. apply FInstantiation .||. apply Instantiation
gt2 = narr .||. apply FInstantiation .||. inst

-- | Take the largest fixpoint of a strategy.
lfp :: (IsMZero mp, Traversable mp, Eq a) => (a -> Proof info mp a) -> a -> Proof info mp a
lfp strat prob = do
  let proof = strat prob
  case proof of
      (F.toList -> [prob']) | prob == prob' -> return prob
      _ | isFailedLayer proof -> return prob
      _ -> do
       prob' <- proof
       if prob == prob' then return prob else lfp strat prob'

-- | Take the largest fixpoint of a strategy, bounded.
lfpBounded :: (IsMZero mp, Traversable mp, Eq a) => Int -> (a -> Proof info mp a) -> a -> Proof info mp a
lfpBounded 0 strat prob = return prob
lfpBounded n strat prob = do
  let proof = strat prob
  case proof of
      (F.toList -> [prob']) | prob == prob' -> return prob
      _ | isFailedLayer proof -> return prob
      _ -> do
       prob' <- proof
       if prob == prob' then return prob else lfpBounded (n-1) strat prob'

isFailedLayer proof =
  case proof of
            Impure DontKnow{} -> True
            Impure (Search m) -> isMZero m
            _ -> False
