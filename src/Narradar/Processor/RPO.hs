{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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
import Data.Suitable (Suitable)
import Data.Typeable
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import Data.Monoid (Monoid(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Term.Family as Family
import Prelude.Extras

import Narradar.Framework.GraphViz

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..))
import Narradar.Constraints.SAT.Solve ( SAT, EvalM, BIEnv, runEvalM, Var
                                      , smtFFI, satYices, YicesOpts(..))
import qualified Narradar.Constraints.SAT.Solve as Solve
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Constraints.SAT.MonadSAT( Decode(..),Tree,printTree, mapTreeTerms )
import Narradar.Constraints.SAT.RPOAF ( UsableSymbol(..), MkSATSymbol
                                      , RPOSsymbol(..), RPOsymbol(..), LPOSsymbol, LPOsymbol, MPOsymbol
                                      , RPOProblemN, RPOId
                                      , UsableSymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, rpoAF_IGDP'
                                      , theSymbolR, isUsable, usableSymbol, filtering, status
                                      , verifyRPOAF, isCorrect
                                      , omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone)
--import Narradar.Constraints.SAT.RPO   (verifyRPO)
--import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe
import qualified Debug.Trace
import qualified Funsat.RPOCircuit as RPOAF

import Debug.Hoed.Observe

-- -------------------
-- RPO SAT Processor
-- -------------------
--rpo :: (MonadPlus mp, Info info i, Info info o, Processor info RPOProc i o) =>
--       i -> Proof info mp o
--rpo = apply (RPOProc RPOSAF SMTSerial)

runSAT :: (Hashable id, Ord id, Show id) =>
          SATSolver -> SAT (TermF id) Var (EvalM Var a) -> IO (Maybe a)
runSAT Yices = satYices YicesOpts{maxWeight = 20, timeout = Nothing}
-- runS FunSat = solveFun
-- runS FunSatDirect = solveFunDirect
-- runS (Yices1 timeout) = unsafePerformIO . solveYicesDirect YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp  timeout) = unsafePerformIO . solveYicesSimp YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp1 timeout) = unsafePerformIO . solveYicesSimp1 YicesOpts{maxWeight = 20, timeout = Just 60}
type AllowCol = Bool
data RPOProc (info :: * -> *) where
  RPOProc :: Extension -> UsableRulesMode -> Solver -> AllowCol -> RPOProc info
type instance InfoConstraint (RPOProc info) = info

instance Observable (RPOProc info) where observer = observeOpaque "RPO processor"

{-
  Some combinations are not safe. The ones I am aware of right now:
   - Existentials are only safe in the SMTFFI backed. Therefore:
   - SMTSerial cannot do MPO because the MPO encoding uses existentials
   - Some of the LPOS encodings have existentials disabled. Ideally we
   - would enable them only in the FFI encoding

 -}
data Extension       = RPOSAF | RPOAF | LPOSAF | LPOAF | MPOAF
data UsableRulesMode = None | Usable | Needed
data Solver          = SMTFFI | SMTSerial -- | SAT SATSolver
data SATSolver       = Yices | Minisat | Funsat

smtSerial :: (FrameworkId id
             ) => Solve.SMTY id Var (EvalM Var (a,b,[id])) -> IO (Maybe (a,b,[id]))
smtSerial = Solve.smtSerial MonadSAT.V

procAF' p ur run = fmap (mapFramework getConstant) $ procAF (mapFramework Constant p) ur run

instance ( Info info (RPOProof id)
         , Info info (Problem (Constant Rewriting (TermF id)) (NTRS id))
         , FrameworkId id, Show id
--         , FrameworkProblemN (Constant Rewriting (TermN id)) id
         ) => Processor (RPOProc info) (NProblem Rewriting id)
   where
    type Typ (RPOProc info) (NProblem Rewriting id) = Rewriting
    type Trs (RPOProc info) (NProblem Rewriting id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules SMTFFI    allowCol) p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial .). rpoAF_DP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF' p RPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)
    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.mpo)


instance (FrameworkId id
         ,Info info (RPOProof id)
         ,Info info (Problem (Constant IRewriting (TermF id)) (NTRS id))
--         ,FrameworkProblemN (Constant IRewriting (TermN id)) id
         ) => Processor (RPOProc info) (NProblem IRewriting id)
   where
    type Typ (RPOProc info) (NProblem IRewriting id) = IRewriting
    type Trs (RPOProc info) (NProblem IRewriting id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF' p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF' p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.mpo)

instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (RPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (RPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules SMTFFI allowCol)    p = procAF p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF p usablerules ((smtFFI.) . rpoAF_DP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF p usablerules ((runSAT s .). rpoAF_DP allowCol RPOAF.mpo)


instance (Info info (RPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procAF_IG p usableRules ((smtFFI.)   . rpoAF_IGDP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF_IG p usablerules ((smtSerial .). rpoAF_IGDP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF_IG p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF_IG p usablerules ((smtFFI.)   . rpoAF_IGDP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF_IG p usablerules ((smtSerial.). rpoAF_IGDP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF_IG p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF_IG p usablerules ((smtFFI.)   . rpoAF_IGDP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF_IG p usablerules ((smtSerial.). rpoAF_IGDP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF_IG p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF_IG p usablerules ((smtFFI.)   . rpoAF_IGDP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF_IG p usablerules ((smtSerial.). rpoAF_IGDP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF_IG p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF_IG p usablerules ((smtFFI.)   . rpoAF_IGDP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF_IG p usablerules ((smtSerial.). rpoAF_IGDP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IG p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.mpo)

instance (Info info (RPOProof id)
         ,Info info (NProblem IRewriting id)
         ,Info info (Problem (Constant IRewriting (TermF id)) (NTRS id))
         ,FrameworkProblemN IRewriting id
--         ,FrameworkProblemN (Constant IRewriting (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) IRewriting) id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = InitialGoal (TermF id) IRewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usableRules ((smtFFI.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p RPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p LPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IG p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.mpo)


instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procAF_IGgen p usableRules ((smtFFI.)   . rpoAF_IGDP' allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF_IGgen p usablerules ((smtSerial.) . rpoAF_IGDP' allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF_IGgen p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF_IGgen p usablerules ((smtFFI.)   . rpoAF_IGDP' allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF_IGgen p usablerules ((smtSerial.). rpoAF_IGDP' allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF_IGgen p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF_IGgen p usablerules ((smtFFI.)   . rpoAF_IGDP' allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF_IGgen p usablerules ((smtSerial.). rpoAF_IGDP' allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF_IGgen p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF_IGgen p usablerules ((smtFFI.)   . rpoAF_IGDP' allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF_IGgen p usablerules ((smtSerial.). rpoAF_IGDP' allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF_IGgen p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF_IGgen p usablerules ((smtFFI.)   . rpoAF_IGDP' allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF_IGgen p usablerules ((smtSerial.). rpoAF_IGDP' allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IGgen p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.mpo)


instance (Info info (RPOProof id)
         ,Info info (NProblem INarrowingGen id)
         ,Info info (Problem (Constant INarrowingGen (TermF id)) (NTRS id))
         ,FrameworkProblemN INarrowingGen id
--         ,FrameworkProblemN (Constant INarrowingGen (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) INarrowingGen) id
         ,GenSymbol id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = InitialGoal (TermF id) INarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usableRules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p usablerules ((smtFFI.)   . rpoAF_DP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p usablerules ((smtSerial.). rpoAF_DP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p usablerules ((runSAT s .). rpoAF_IGDP allowCol RPOAF.mpo)


instance (Info info (RPOProof id)
         ,FrameworkId id
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    applyO _ (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procNAF p usableRules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.mpo)


instance (FrameworkId  id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    applyO _ (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procNAF p usableRules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.rpos)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.rpos)

    applyO _ (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.rpo)
    applyO _ (RPOProc RPOAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.rpo)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.rpo)

    applyO _ (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.lpos)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.lpos)

    applyO _ (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.lpo)
    applyO _ (RPOProc LPOAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.lpo)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.lpo)

    applyO _ (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procNAF p usablerules ((smtFFI.)   . rpoAF_NDP allowCol RPOAF.mpo)
    applyO _ (RPOProc MPOAF usablerules SMTSerial allowCol) p = procNAF p usablerules ((smtSerial.). rpoAF_NDP allowCol RPOAF.mpo)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procNAF p usablerules ((runSAT s .). rpoAF_NDP allowCol RPOAF.mpo)

-- -----------------
-- Implementations
-- -----------------

wsatYices tm = satYices YicesOpts{maxWeight = 20, timeout = Just tm}
{-
procAF' :: (Monad m
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


{-
procAF' :: ( id  ~ Family.Var repr
          , Var ~ Family.Var id
          , t   ~ Family.TermF repr
          , t   ~ TermF id
          , RPOAF.CoRPO repr t Narradar.Var Var
          , RPOAF.RPOCircuit repr
          , MonadSAT.ECircuit repr
          , UsableSymbol id
          , RPOAF.HasFiltering id, RPOAF.HasPrecedence id, RPOAF.HasStatus id
          , NeededRules  typ (NTRS id)
          , IUsableRules typ (NTRS id)
          , HasMinimality typ
          , MkDPProblem typ (NTRS id)
          , Traversable (Problem typ)
          , Ord id, Pretty id
          , Decode id (UsableSymbolRes id)
          , Suitable info (RPOProof id)
          , Suitable info (NProblem typ id)
          , Applicative info
          , Monad m
          ) =>
          NProblem typ id ->
          Extension sid  ->
          UsableRules ->
          ((NProblem typ sid -> repr Var) ->
           NProblem typ id ->
           IO (Maybe([Int], BIEnv Var, [sid]))) ->
          Proof info m (NProblem typ id)
-}
procAF p usablerules run = (f . unsafePerformIO . run omega) p
 where
  omega = case usablerules of
            Needed -> omegaNeeded
            Usable -> omegaUsable
            None   -> omegaNone

  f Nothing = dontKnow (rpoFail p) p
  f (Just (nondec_dps, bienv, symbols_raw)) = singleP proof p p'
   where
    symbols       = runEvalM bienv $ mapM decode symbols_raw
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
{-
procAF_IG ::
  forall info typ base id sid repr e a m .
                ( Decode a (UsableSymbolRes sid)
                , FrameworkProblemN typ sid
                , RPOId id
                , ExpandDPair (InitialGoal (TermF id) base) (NTRS id)
                , ExpandDPair base (NTRS id)
                , InsertDPairs (InitialGoal (TermF id) base) (NTRS id)
                , InsertDPairs base (NTRS id)
                , PprTPDB (NProblem base id)
                , Suitable info (RPOProof sid)
                , Suitable info (NProblem typ sid)
                , Applicative info, Ord1 info, Typeable info
                , Monad m
                , Family.Var id  ~ Var
                , Family.TermF repr ~ TermF id
                , RPOAF.CoRPO repr (TermF id) Narradar.Var Var
                , RPOAF.RPOExtCircuit repr id
                , MonadSAT.ECircuit repr
                ) => NProblem typ sid
                  -> SExtension e
                  -> UsableRulesMode
                  -> ((NProblem (InitialGoal (TermF id) base) id
                       -> (repr Var, EvalM Var [Tree (TermN id) Var]))
                       -> NProblem typ sid
                       -> IO (Maybe (([Int], [Tree (TermN sid) Var]), BIEnv (Family.Var a), [a])))
                  -> Proof info m (NProblem typ sid)
-}
procAF_IG p usablerules run = (f . unsafePerformIO . run omega) p where
 omega = case usablerules of
            Needed -> omegaIG
            Usable -> omegaIG
--            None   -> omegaNone

 f Nothing = dontKnow (rpoFail p) p
 f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p)
  where
   symbols       = runEvalM bienv $ mapM decode symbols_raw
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

procAF_IGgen ::
  forall info typ base id sid m e .
                ( Decode id (UsableSymbolRes sid)
                , FrameworkProblemN typ sid
                , RPOId id, GenSymbol id
                , ExpandDPair (InitialGoal (TermF id) base) (NTRS id)
                , ExpandDPair base (NTRS id)
                , InsertDPairs (InitialGoal (TermF id) base) (NTRS id)
                , InsertDPairs base (NTRS id)
                , PprTPDB (NProblem base id)
                , Suitable info (RPOProof sid)
                , Suitable info (NProblem typ sid)
                , Applicative info, Ord1 info, Typeable info
                , Monad m
                , Family.Var id  ~ Var
                ) => NProblem typ sid
                  -> UsableRulesMode
                  -> ((NProblem (InitialGoal (TermF id) base) id
                            -> (Tree (TermN id) Var, EvalM Var [Tree (TermN id) Var]))
                       -> NProblem typ sid
                       -> IO (Maybe (([Int], [Tree (TermN sid) Var]), BIEnv Var, [id])))
                  -> Proof info m (NProblem typ sid)

procAF_IGgen p usablerules run = (f . unsafePerformIO . run omega) p where
  omega = case usablerules of
            Needed -> omegaIGgen
            Usable -> omegaIGgen
--            None   -> omegaNone
  f Nothing = dontKnow (rpoFail p) p
  f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p) where

   symbols       = runEvalM bienv $ mapM decode (symbols_raw)
   proof         = RPOAFExtraProof decreasingDps usableRules symbols extraConstraints'
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO"
                        ([0..length (rules dps) - 1] \\ nondec_dps)
                        (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
   extraConstraints' :: [Tree (TermN sid) Var]
   extraConstraints' = mapTreeTerms (mapTermSymbols id) <$> extraConstraints

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
procNAF p usablerules run =
 case usablerules of
            Needed -> (f . unsafePerformIO . run omegaNeeded) p
            Usable -> (f . unsafePerformIO . run omegaUsable) p
            None   -> (f . unsafePerformIO . run omegaNone) p
   where
 f Nothing = dontKnow (rpoFail p) p
 f (Just ((non_dec_dps, non_rhsground_dps), bienv, symbols_raw)) =
    let proof = RPOAFProof decreasingDps usableRules symbols
        symbols       = runEvalM bienv $ mapM decode (symbols_raw)
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
                -> [UsableSymbolRes id]
                -> RPOProof id

     RPOAFExtraProof
                :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [UsableSymbolRes id]
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

     deriving Typeable

instance (Ord id, Pretty id) => Eq (RPOProof id) where a == b = pPrint a == pPrint b
instance (Ord id, Pretty id) => Ord (RPOProof id) where compare a b = pPrint a `compare` pPrint b
instance Observable1 RPOProof where observer1 = observeOpaque "RPOProof"
instance Observable a => Observable (RPOProof a) where observer = observer1 ; observers = observers1

rpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> RPOProof (Family.Id t)
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
        text "Precedence:" <+> printPrec RPOAF.prec theSymbolR ssPrec $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status s of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s <- ssPrec])
     where
       the_af = AF.fromList' [(theSymbolR s, filtering s) | s <- ss]
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

-- Nil instance
instance Ord a => RemovePrologId (RPOAF.Usable a) where
  type WithoutPrologId (RPOAF.Usable a) = RPOAF.Usable a
  removePrologId = Just
