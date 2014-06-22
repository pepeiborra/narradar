{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
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
import Narradar.Constraints.SAT.RPOAF ( SATSymbol, UsableSymbol(..)
                                      , RPOSsymbol(..), RPOsymbol(..), LPOSsymbol, LPOsymbol, MPOsymbol
                                      , RPOProblemN, RPOId
                                      , UsableSymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP
                                      , theSymbolR, isUsable, filtering, status
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
import Data.Functor.Constant (Constant(..))

runSAT :: (Hashable id, Ord id, Show id) =>
          SATSolver -> SAT (TermF id) Var (EvalM Var a) -> IO (Maybe a)
runSAT Yices = satYices YicesOpts{maxWeight = 20, timeout = Nothing}
-- runS FunSat = solveFun
-- runS FunSatDirect = solveFunDirect
-- runS (Yices1 timeout) = unsafePerformIO . solveYicesDirect YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp  timeout) = unsafePerformIO . solveYicesSimp YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp1 timeout) = unsafePerformIO . solveYicesSimp1 YicesOpts{maxWeight = 20, timeout = Just 60}
type AllowCol = Bool
data RPOProc (info :: * -> *) where RPOProc :: SATSymbol e => Extension e -> UsableRulesMode -> Solver -> AllowCol -> RPOProc info
type instance InfoConstraint (RPOProc info) = info

{-
  Some combinations are not safe. The ones I am aware of right now:
   - Existentials are only safe in the SMTFFI backed. Therefore:
   - SMTSerial cannot do MPO because the MPO encoding uses existentials
   - Some of the LPOS encodings have existentials disabled. Ideally we
   - would enable them only in the FFI encoding

 -}
data Extension a where
    RPOSAF :: Extension (RPOAF.Usable(RPOSsymbol v id))
    RPOAF  :: Extension (RPOAF.Usable(RPOsymbol  v id))
    LPOSAF :: Extension (RPOAF.Usable(LPOSsymbol v id))
    LPOAF  :: Extension (RPOAF.Usable(LPOsymbol  v id))
    MPOAF  :: Extension (RPOAF.Usable(MPOsymbol  v id))
data UsableRulesMode = None | Usable | Needed
data Solver    = SMTFFI | SMTSerial -- | SAT SATSolver
data SATSolver = Yices | Minisat | Funsat

smtSerial = Solve.smtSerial MonadSAT.V
procAF' p ex ur run = fmap (mapFramework getConstant) $ procAF (mapFramework Constant p) ex ur run

instance (Info info (RPOProof id)
         , FrameworkId id, Show id
         ) => Processor (RPOProc info) (NProblem Rewriting id)
   where
    type Typ (RPOProc info) (NProblem Rewriting id) = Rewriting
    type Trs (RPOProc info) (NProblem Rewriting id) = NTRS id
    apply (RPOProc RPOSAF usablerules SMTFFI    allowCol) p = procAF' p RPOSAF usablerules ((smtFFI.) . rpoAF_DP allowCol)

    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF' p RPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF' p RPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF' p RPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF' p RPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF' p RPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF' p LPOSAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF' p LPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF' p LPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF' p LPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF' p LPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF' p LPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF' p MPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF' p MPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF' p MPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)


instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem IRewriting id)
   where
    type Typ (RPOProc info) (NProblem IRewriting id) = IRewriting
    type Trs (RPOProc info) (NProblem IRewriting id) = NTRS id
    apply (RPOProc RPOSAF usablerules SMTFFI allowCol)    p = procAF' p RPOSAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF' p RPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF' p RPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF' p RPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF' p RPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF' p RPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF' p LPOSAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF' p LPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF' p LPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF' p LPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF' p LPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF' p LPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF' p MPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF' p MPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF' p MPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (RPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (RPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    apply (RPOProc RPOSAF usablerules SMTFFI allowCol)    p = procAF p RPOSAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF p RPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF p RPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF p RPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF p RPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF p RPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF p LPOSAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF p LPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF p LPOSAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF p LPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF p LPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF p LPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF p MPOAF usablerules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF p MPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF p MPOAF usablerules ((runSAT s .). rpoAF_DP allowCol)


instance (Info info (RPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procAF_IG p RPOSAF usableRules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF_IG p RPOSAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF_IG p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF_IG p RPOAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF_IG p RPOAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF_IG p RPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF_IG p LPOSAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF_IG p LPOSAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF_IG p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF_IG p LPOAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF_IG p LPOAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF_IG p LPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF_IG p MPOAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF_IG p MPOAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IG p MPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

instance (Info info (RPOProof id)
         ,Info info (NProblem IRewriting id)
         ,FrameworkProblemN (InitialGoal (TermF id) IRewriting) id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = InitialGoal (TermF id) IRewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p RPOSAF usableRules ((smtFFI.) . rpoAF_DP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p RPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p RPOAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p RPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p RPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p LPOSAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p LPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p LPOAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p LPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF'_IG p LPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p MPOAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p MPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IG p MPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

{-
instance (Show id, Ord id, Pretty id, DPSymbol id, Hashable id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procAF_IGgen p RPOSAF usableRules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procAF_IGgen p RPOSAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procAF_IGgen p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procAF_IGgen p RPOAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procAF_IGgen p RPOAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procAF_IGgen p RPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procAF_IGgen p LPOSAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procAF_IGgen p LPOSAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procAF_IGgen p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procAF_IGgen p LPOAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procAF_IGgen p LPOAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procAF_IGgen p LPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procAF_IGgen p MPOAF usablerules ((smtFFI.)   . rpoAF_IGDP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procAF_IGgen p MPOAF usablerules ((smtSerial.). rpoAF_IGDP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procAF_IGgen p MPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)
-- -}

instance (Info info (RPOProof id)
         ,Info info (NProblem INarrowingGen id)
         ,FrameworkProblemN (InitialGoal (TermF id) INarrowingGen) id
         ,GenSymbol id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = InitialGoal (TermF id) INarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = NTRS id
    apply (RPOProc RPOSAF usableRules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p RPOSAF usableRules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p RPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p RPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p RPOAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p RPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p RPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p LPOSAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p LPOSAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p LPOSAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p LPOAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p LPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p LPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    = liftProblem $ \p -> procAF' p MPOAF usablerules ((smtFFI.)   . rpoAF_DP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) = liftProblem $ \p -> procAF' p MPOAF usablerules ((smtSerial.). rpoAF_DP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   = liftProblem $ \p -> procAF' p MPOAF usablerules ((runSAT s .). rpoAF_IGDP allowCol)


instance (Info info (RPOProof id)
         ,FrameworkId id
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    apply (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procNAF p RPOSAF usableRules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procNAF p RPOSAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procNAF p RPOSAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procNAF p RPOAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procNAF p RPOAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procNAF p RPOAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procNAF p LPOSAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procNAF p LPOSAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procNAF p LPOSAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procNAF p LPOAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procNAF p LPOAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procNAF p LPOAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procNAF p MPOAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procNAF p MPOAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procNAF p MPOAF usablerules ((runSAT s .). rpoAF_NDP allowCol)


instance (FrameworkId  id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    apply (RPOProc RPOSAF usableRules SMTFFI allowCol)    p = procNAF p RPOSAF usableRules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc RPOSAF usablerules SMTSerial allowCol) p = procNAF p RPOSAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc RPOSAF usablerules (SAT s))   p = procNAF p RPOSAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc RPOAF usablerules SMTFFI allowCol)    p = procNAF p RPOAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc RPOAF usablerules SMTSerial allowCol) p = procNAF p RPOAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc RPOAF usablerules (SAT s))   p = procNAF p RPOAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc LPOSAF usablerules SMTFFI allowCol)    p = procNAF p LPOSAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc LPOSAF usablerules SMTSerial allowCol) p = procNAF p LPOSAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc LPOSAF usablerules (SAT s))   p = procNAF p LPOSAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc LPOAF usablerules SMTFFI allowCol)    p = procNAF p LPOAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc LPOAF usablerules SMTSerial allowCol) p = procNAF p LPOAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc LPOAF usablerules (SAT s))   p = procNAF p LPOAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

    apply (RPOProc MPOAF usablerules SMTFFI allowCol)    p = procNAF p MPOAF usablerules ((smtFFI.)   . rpoAF_NDP allowCol)
    apply (RPOProc MPOAF usablerules SMTSerial allowCol) p = procNAF p MPOAF usablerules ((smtSerial.). rpoAF_NDP allowCol)
--    apply (RPOProc MPOAF usablerules (SAT s))   p = procNAF p MPOAF usablerules ((runSAT s .). rpoAF_NDP allowCol)

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

fixExtension :: Extension e -> [e] -> [e]
fixExtension _ = id

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


procAF_IGgen :: ( Decode a (UsableSymbolRes sid)
                , RPOProblemN base id
                , RPOProblemN (InitialGoal (TermF id) base) id
                , RPOProblemN typ sid
                , Suitable info (RPOProof sid)
                , Suitable info (NProblem typ sid)
                , Applicative info
                , Monad m
                , Family.Var id ~ Var
                ) => Problem typ (NTRS sid)
                  -> Extension a
                  -> UsableRulesMode
                  -> ((NProblem (InitialGoal (TermF id) base) id
                       -> (Tree (TermN id) Var, EvalM Var [Tree (TermN id) Var]))
                       -> Problem typ (NarradarTRS (TermF sid) Narradar.Var)
                       -> IO (Maybe (([Int], [Tree (TermN sid) Var]), BIEnv (Family.Var a), [a])))
                  -> Proof info m (Problem typ (NarradarTRS (TermF sid) Narradar.Var))
procAF_IGgen p e usablerules run = (f . unsafePerformIO . run omega) p where
  omega = case usablerules of
            Needed -> omegaIGgen
            Usable -> omegaIGgen
--            None   -> omegaNone
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
   theSymbol = id -- head . F.toList

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
