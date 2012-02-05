{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}

module Narradar.Processor.RPO where

import Control.Applicative
import Control.DeepSeq
import Control.Exception as CE (assert)
import Control.Monad
import Control.Parallel.Strategies
import Data.Bifunctor
import Data.Foldable as F (Foldable, toList)
import Data.Traversable (Traversable)
import Data.Hashable
import Data.Typeable
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import Data.Monoid (Monoid(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Term.Family as Family

import Narradar.Framework.GraphViz

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO
import Narradar.Constraints.SAT.Solve ( SAT, EvalM, BIEnv, runEvalM, decode, Var
                                      , smtSerial, smtFFI, satYices, YicesOpts(..))
import Narradar.Constraints.SAT.MonadSAT( Decode,Tree,printTree, mapTreeTerms )
import Narradar.Constraints.SAT.RPOAF ( SATSymbol
                                      , RPOSsymbol(..), RPOsymbol(..), LPOSsymbol, LPOsymbol, MPOsymbol
                                      , SymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP
                                      , isUsable, theSymbolR, filtering
                                      , verifyRPOAF, isCorrect
                                      , omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone)
--import Narradar.Constraints.SAT.RPO   (verifyRPO)
--import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe
import qualified Debug.Trace

-- -------------------
-- RPO SAT Processor
-- -------------------
--rpo :: (MonadPlus mp, Info info i, Info info o, Processor info RPOProc i o) =>
--       i -> Proof info mp o
--rpo = apply (RPOProc RPOSAF SMTSerial)

runSAT :: (Hashable id, Ord id, Show id) => SATSolver -> SAT (TermN id) Var (EvalM Var a) -> IO (Maybe a)
runSAT Yices = satYices YicesOpts{maxWeight = 20, timeout = Nothing}
-- runS FunSat = solveFun
-- runS FunSatDirect = solveFunDirect
-- runS (Yices1 timeout) = unsafePerformIO . solveYicesDirect YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp  timeout) = unsafePerformIO . solveYicesSimp YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp1 timeout) = unsafePerformIO . solveYicesSimp1 YicesOpts{maxWeight = 20, timeout = Just 60}

data RPOProc (info :: * -> *) where RPOProc :: SATSymbol e => Extension e -> UsableRules -> Solver -> RPOProc info
type instance InfoConstraint (RPOProc info) = info
data Extension a where
    RPOSAF :: Extension RPOSsymbol
    RPOAF  :: Extension RPOsymbol
    LPOSAF :: Extension LPOSsymbol
    LPOAF  :: Extension LPOsymbol
    MPOAF  :: Extension MPOsymbol
data UsableRules = None | Usable | Needed
data Solver    = SMTFFI | SMTSerial -- | SAT SATSolver
data SATSolver = Yices | Minisat | Funsat


instance (Ord id, Pretty id, DPSymbol id, Show id, Hashable id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem Rewriting id)
   where
    type Typ (RPOProc info) (NProblem Rewriting id) = Rewriting
    type Trs (RPOProc info) (NProblem Rewriting id) = NTRS id
    apply (RPOProc RPOSAF usablerules SMTFFI)    p = procAF p RPOSAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) p = procAF p RPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF p RPOSAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    p = procAF p RPOAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) p = procAF p RPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF p RPOAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    p = procAF p LPOSAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) p = procAF p LPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF p LPOSAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    p = procAF p LPOAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) p = procAF p LPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF p LPOAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    p = procAF p MPOAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) p = procAF p MPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF p MPOAF usablerules ((runSAT s .). rpoAF_DP True)


instance (Ord id, Pretty id, DPSymbol id, Show id, Hashable id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem IRewriting id)
   where
    type Typ (RPOProc info) (NProblem IRewriting id) = IRewriting
    type Trs (RPOProc info) (NProblem IRewriting id) = NTRS id
    apply (RPOProc RPOSAF usablerules SMTFFI)    p = procAF p RPOSAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) p = procAF p RPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF p RPOSAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    p = procAF p RPOAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) p = procAF p RPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF p RPOAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    p = procAF p LPOSAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) p = procAF p LPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF p LPOSAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    p = procAF p LPOAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) p = procAF p LPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF p LPOAF usablerules ((runSAT s .). rpoAF_DP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    p = procAF p MPOAF usablerules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) p = procAF p MPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF p MPOAF usablerules ((runSAT s .). rpoAF_DP True)


instance (Show id, Ord id, Pretty id, DPSymbol id, Hashable id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI)    p = procAF_IG p RPOSAF usableRules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) p = procAF_IG p RPOSAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF_IG p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    p = procAF_IG p RPOAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) p = procAF_IG p RPOAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF_IG p RPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    p = procAF_IG p LPOSAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) p = procAF_IG p LPOSAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF_IG p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    p = procAF_IG p LPOAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) p = procAF_IG p LPOAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF_IG p LPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    p = procAF_IG p MPOAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) p = procAF_IG p MPOAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IG p MPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

instance (Show id, Ord id, Pretty id, DPSymbol id, Hashable id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ,Info info (NProblem IRewriting id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = InitialGoal (TermF id) IRewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI)    = liftProblem $ \p -> procAF p RPOSAF usableRules ((smtFFI.) . rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) = liftProblem $ \p -> procAF p RPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF_IG p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p RPOAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) = liftProblem $ \p -> procAF p RPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF_IG p RPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p LPOSAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) = liftProblem $ \p -> procAF p LPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF_IG p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p LPOAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) = liftProblem $ \p -> procAF p LPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF_IG p LPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p MPOAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) = liftProblem $ \p -> procAF p MPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IG p MPOAF usablerules ((runSAT s .). rpoAF_IGDP True)


instance (Show id, Ord id, Pretty id, DPSymbol id, Hashable id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI)    p = procAF_IGgen p RPOSAF usableRules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) p = procAF_IGgen p RPOSAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF_IGgen p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    p = procAF_IGgen p RPOAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) p = procAF_IGgen p RPOAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF_IGgen p RPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    p = procAF_IGgen p LPOSAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) p = procAF_IGgen p LPOSAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF_IGgen p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    p = procAF_IGgen p LPOAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) p = procAF_IGgen p LPOAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF_IGgen p LPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    p = procAF_IGgen p MPOAF usablerules ((smtFFI.)   . rpoAF_IGDP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) p = procAF_IGgen p MPOAF usablerules ((smtSerial.). rpoAF_IGDP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IGgen p MPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

instance (Show id, Ord id, Pretty id, DPSymbol id, Hashable id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ,Info info (NProblem INarrowingGen id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = InitialGoal (TermF id) INarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI)    = liftProblem $ \p -> procAF p RPOSAF usableRules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) = liftProblem $ \p -> procAF p RPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p RPOAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) = liftProblem $ \p -> procAF p RPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF p RPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p LPOSAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) = liftProblem $ \p -> procAF p LPOSAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p LPOAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) = liftProblem $ \p -> procAF p LPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF p LPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    = liftProblem $ \p -> procAF p MPOAF usablerules ((smtFFI.)   . rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) = liftProblem $ \p -> procAF p MPOAF usablerules ((smtSerial.). rpoAF_DP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF p MPOAF usablerules ((runSAT s .). rpoAF_IGDP True)

instance (Ord id, Pretty id, DPSymbol id, Show id, Hashable id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    apply (RPOProc RPOSAF usableRules SMTFFI)    p = procNAF p RPOSAF usableRules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) p = procNAF p RPOSAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procNAF p RPOSAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    p = procNAF p RPOAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) p = procNAF p RPOAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procNAF p RPOAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    p = procNAF p LPOSAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) p = procNAF p LPOSAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procNAF p LPOSAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    p = procNAF p LPOAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) p = procNAF p LPOAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procNAF p LPOAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    p = procNAF p MPOAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) p = procNAF p MPOAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procNAF p MPOAF usablerules ((runSAT s .). rpoAF_NDP True)


instance (Ord id, Pretty id, DPSymbol id, Show id, Hashable id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    apply (RPOProc RPOSAF usableRules SMTFFI)    p = procNAF p RPOSAF usableRules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc RPOSAF usablerules SMTSerial) p = procNAF p RPOSAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procNAF p RPOSAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc RPOAF usablerules SMTFFI)    p = procNAF p RPOAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc RPOAF usablerules SMTSerial) p = procNAF p RPOAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procNAF p RPOAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc LPOSAF usablerules SMTFFI)    p = procNAF p LPOSAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc LPOSAF usablerules SMTSerial) p = procNAF p LPOSAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procNAF p LPOSAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc LPOAF usablerules SMTFFI)    p = procNAF p LPOAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc LPOAF usablerules SMTSerial) p = procNAF p LPOAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procNAF p LPOAF usablerules ((runSAT s .). rpoAF_NDP True)

    apply (RPOProc MPOAF usablerules SMTFFI)    p = procNAF p MPOAF usablerules ((smtFFI.)   . rpoAF_NDP True)
--    apply (RPOProc MPOAF usablerules SMTSerial) p = procNAF p MPOAF usablerules ((smtSerial.). rpoAF_NDP True)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procNAF p MPOAF usablerules ((runSAT s .). rpoAF_NDP True)

-- -----------------
-- Implementations
-- -----------------

wsatYices tm = satYices YicesOpts{maxWeight = 20, timeout = Just tm}
{-
procAF :: (Monad m
          ,sres  ~ SymbolRes id
          ,sid   ~ satsymbol Var id
          ,Info info (NProblem typ id)
          ,Info info (RPOProof id)
          ,Pretty id, Ord id, Hashable id
          ,Traversable  (Problem typ)
          ,MkDPProblem typ (NTRS id)
          ,Decode sid (SymbolRes id) Var
          )=> NProblem typ id
           -> Extension satsymbol
           -> UsableRules
           -> ((NProblem typ sid -> repr Var) -> NProblem typ id -> IO (Maybe ([Int], BIEnv Var, [sid])))
           -> Proof info m (NProblem typ id)
-}

fixExtension :: Extension e -> [e Var id] -> [e Var id]
fixExtension _ = id

procAF p e usablerules run = (f . unsafePerformIO . run omega) p
 where
  omega = case usablerules of
            Needed -> omegaNeeded
            Usable -> omegaUsable
            None   -> omegaNone

  f Nothing = dontKnow (rpoFail p) p
  f (Just (nondec_dps, bienv, symbols_raw)) = singleP proof p p'
   where
    symbols       = runEvalM bienv $ mapM decode (fixExtension e symbols_raw)
    proof         = RPOAFProof decreasingDps usableRules symbols
    dps           = getP p
    decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
    usableRules   = [ r | r <- rules(getR p)
                        , let Just f = rootSymbol (lhs r)
                        , f `Set.member` usableSymbols]
    usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
    p'            = setP (restrictTRS dps nondec_dps) p

{-
   verification  = forDPProblem verifyRPOAF p symbols nondec_dps
   isValidProof
     | isCorrect verification = True
     | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False

   CE.assert isValidProof $
-}

procAF_IG p e usablerules run = (f . unsafePerformIO . run omega) p where
 omega = case usablerules of
            Needed -> omegaIG
            Usable -> omegaIG
--            None   -> omegaNone

 f Nothing = dontKnow (rpoFail p) p
 f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p)
  where
   symbols       = runEvalM bienv $ mapM decode (fixExtension e symbols_raw)
   proof         = RPOAFProof decreasingDps usableRules symbols
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
{-
   verification  = runEvalM bienv $ verifyRPOAF typSymbols rrSymbols dpsSymbols nondec_dps
   typSymbols    = mapInitialGoal (bimap convertSymbol id) (getProblemType p)
   rrSymbols     = mapNarradarTRS (mapTermSymbols convertSymbol) (getR p)
   dpsSymbols    = mapNarradarTRS (mapTermSymbols convertSymbol) (getP p)
   convertSymbol = fromJust . (`Map.lookup` Map.fromList
                                            [(theSymbolR(runEvalM bienv $ decode s), s)
                                                 | s <- symbols_raw])
   isValidProof
    | isCorrect verification = True
    | otherwise = Debug.Trace.trace (show (proof $+$ Ppr.empty $+$ verification)) False
-}


procAF_IGgen p e usablerules run
  = case usablerules of
            Needed -> (f . unsafePerformIO . run omegaIGgen) p
            Usable -> (f . unsafePerformIO . run omegaIGgen) p
--            None   -> omegaNone
 where
  f Nothing = dontKnow (rpoFail p) p
  f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p) where

   symbols       = runEvalM bienv $ mapM decode (fixExtension e symbols_raw)
   proof         = RPOAFExtraProof decreasingDps usableRules symbols extraConstraints'
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
   extraConstraints' = mapTreeTerms (mapTermSymbols theSymbol) <$> extraConstraints
   theSymbol = head . F.toList

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
procNAF p e usablerules run =
 case usablerules of
            Needed -> (f . unsafePerformIO . run omegaNeeded) p
            Usable -> (f . unsafePerformIO . run omegaUsable) p
            None   -> (f . unsafePerformIO . run omegaNone) p
   where
 f Nothing = dontKnow (rpoFail p) p
 f (Just ((non_dec_dps, non_rhsground_dps), bienv, symbols_raw)) =
    let proof = RPOAFProof decreasingDps usableRules symbols
        symbols       = runEvalM bienv $ mapM decode (fixExtension e symbols_raw)
        decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ non_dec_dps) (rules dps)
        usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
        usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
        p1            = setP (restrictTRS dps non_dec_dps) p
        p2            = setP (restrictTRS dps non_rhsground_dps) p
    in andP proof p (snub [p1,p2])
       where dps = getP p
{-
proc :: ( Pretty id
        , Info info (RPOProof id), Info info (NarradarProblem typ t)
        , IsDPProblem typ, Monad m
        ) =>
        NarradarProblem typ t -> IO (Maybe ([Int], [RPO.SymbolRes id]))
     -> Proof info m (NarradarProblem typ t)

proc p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (nondec_dps, symbols) ->
                      let proof         = RPOProof decreasingDps [] symbols
                          dps           = getP p
                          decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
                          p'            = setP (restrictTRS dps nondec_dps) p
                          verification  = verifyRPO p symbols nondec_dps
                          isValidProof
                            | isCorrect verification = True
                            | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False
                      in
                         CE.assert isValidProof $
                         singleP proof p p'
-}
-- -------------
-- RPO Proofs
-- -------------

data RPOProof id where
     RPOAFProof :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [RPOAF.SymbolRes id]
                -> RPOProof id

     RPOAFExtraProof
                :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [RPOAF.SymbolRes id]
                -> [Tree (TermN id) Var] -- ^ Extra constraints
                -> RPOProof id
{-
     RPOProof   :: Pretty (Rule t v) =>
                   [Rule t v]       --  ^ Strictly Decreasing dps
                -> [Rule t v]       --  ^ Usable Rules
                -> [RPO.SymbolRes id]
                -> RPOProof id
-}
     RPOFail :: RPOProof id

rpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> RPOProof (Family.Id1 t)
rpoFail _ = RPOFail

instance (Ord id, Pretty id) => Pretty (RPOProof id) where
    pPrint (RPOAFProof dps rr ss) = pPrint (RPOAFExtraProof dps rr ss [])
    pPrint (RPOAFExtraProof dps rr ss cc) =
     (if null cc then text "RPO reduction pair"
        else text "RPO reduction pair with the extra constraints" $$
             nest 4 (vcat $ map (printTree 0) cc))
     $$ text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "The argument filtering used was:" $$
        nest 4 (pPrint the_af) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map pPrint rr) $$
        text "Precedence:" <+> printPrec RPOAF.precedence RPOAF.theSymbolR ssPrec $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPOAF.SymbolRes{..} <- ssPrec])
     where
       the_af = AF.fromList' [(theSymbolR, filtering) | RPOAF.SymbolRes{..} <- ss]
       relevantSymbols = getAllSymbols (dps `mappend` rr)
       ssPrec = [ s | s <- ss, theSymbolR s `Set.member` relevantSymbols]
{-
    pPrint (RPOProof dps _ ss) =
        text "Monotonic RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "Precedence:" <+> printPrec RPO.precedence RPO.theSymbolR ss $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPO.SymbolRes{..} <- ss])
-}
    pPrint RPOFail = text "RPO Reduction Pair : failed to synthetize a suitable ordering"


printPrec f symb    = fsep
                    . punctuate (text " >")
                    . fmap ( fsep
                           . punctuate (text (" ="))
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)