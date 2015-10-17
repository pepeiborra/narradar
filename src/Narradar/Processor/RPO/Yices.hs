{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
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

module Narradar.Processor.RPO.Yices where

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
import Narradar.Constraints.SAT.YicesFFICircuit
import Narradar.Constraints.SAT.MonadSAT( IsSimple, Decode(..),Tree,printTree, mapTreeTerms )
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Constraints.SAT.RPOAF ( UsableSymbol(..), MkSATSymbol
                                      , RPOSsymbol(..), RPOsymbol(..), LPOSsymbol, LPOsymbol, MPOsymbol
                                      , RPOProblemN, RPOId
                                      , UsableSymbolRes
                                      , reductionPair, reductionPairIG, reductionPairN, setupAF
                                      , theSymbolR, isUsable, usableSymbol, filtering, status
                                      , verifyRPOAF, isCorrect
                                      , omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone)
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Processor.RPO
import Narradar.Utils
import System.IO.Unsafe
import qualified Debug.Trace
import qualified Funsat.TermCircuit as RPOAF

import Debug.Hoed.Observe

-- -------------------
-- RPO SAT Processor
-- -------------------
run  mkS cTyp p rpo = runRpoProc  (unsafePerformIO . solve) mkS cTyp rpo p
runN mkS cTyp p rpo = runRpoProcN (unsafePerformIO . solve) mkS cTyp rpo p
omegaFor None = omegaNone
omegaFor Needed = omegaNeeded
omegaFor Usable = omegaUsable

instance ( Info info (RPOProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (RPOProc info) (NProblem (MkRewriting strat) id)
   where
    type Typ (RPOProc info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (RPOProc info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules allowCol) = run RPOAF.rpos RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc LPOSAF usablerules allowCol) = run RPOAF.lpos RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc RPOAF  usablerules allowCol) = run RPOAF.rpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc LPOAF  usablerules allowCol) = run RPOAF.lpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc MPOAF  usablerules allowCol) = run RPOAF.mpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (RPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (RPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules allowCol) = run RPOAF.rpos RPOAF.convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc LPOSAF usablerules allowCol) = run RPOAF.lpos RPOAF.convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc RPOAF  usablerules allowCol) = run RPOAF.rpo  RPOAF.convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc LPOAF  usablerules allowCol) = run RPOAF.lpo  RPOAF.convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (RPOProc MPOAF  usablerules allowCol) = run RPOAF.mpo  RPOAF.convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (Info info (RPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id, IsSimple id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO _ (RPOProc RPOSAF _ allowCol) = run RPOAF.rpos RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (RPOProc LPOSAF _ allowCol) = run RPOAF.lpos RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (RPOProc RPOAF  _ allowCol) = run RPOAF.lpo  RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (RPOProc LPOAF  _ allowCol) = run RPOAF.rpo  RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (RPOProc MPOAF  _ allowCol) = run RPOAF.mpo  RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))

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
    applyO _ (RPOProc RPOSAF usableRules allowCol) = liftProblem (run RPOAF.rpos RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc LPOSAF usableRules allowCol) = liftProblem (run RPOAF.lpos RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc RPOAF  usableRules allowCol) = liftProblem (run RPOAF.rpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc LPOAF  usableRules allowCol) = liftProblem (run RPOAF.lpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc MPOAF  usableRules allowCol) = liftProblem (run RPOAF.mpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))

instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    applyO _ (RPOProc RPOSAF _ allowCol) = run RPOAF.rpos RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (RPOProc LPOSAF _ allowCol) = run RPOAF.lpos RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (RPOProc RPOAF  _ allowCol) = run RPOAF.lpo  RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (RPOProc LPOAF  _ allowCol) = run RPOAF.rpo  RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (RPOProc MPOAF  _ allowCol) = run RPOAF.mpo  RPOAF.convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)

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
    applyO _ (RPOProc RPOSAF usableRules allowCol) = liftProblem (run RPOAF.rpos RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc LPOSAF usableRules allowCol) = liftProblem (run RPOAF.lpos RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc RPOAF  usableRules allowCol) = liftProblem (run RPOAF.rpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc LPOAF  usableRules allowCol) = liftProblem (run RPOAF.lpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (RPOProc MPOAF  usableRules allowCol) = liftProblem (run RPOAF.mpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))


instance (Info info (RPOProof id)
         ,FrameworkId id
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO _ (RPOProc RPOSAF usableRules allowCol) = runN RPOAF.rpos RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc LPOSAF usableRules allowCol) = runN RPOAF.lpos RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc RPOAF  usableRules allowCol) = runN RPOAF.rpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc LPOAF  usableRules allowCol) = runN RPOAF.lpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc MPOAF  usableRules allowCol) = runN RPOAF.mpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

instance (FrameworkId  id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO _ (RPOProc RPOSAF usableRules allowCol) = runN RPOAF.rpos RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc LPOSAF usableRules allowCol) = runN RPOAF.lpos RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc RPOAF  usableRules allowCol) = runN RPOAF.rpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc LPOAF  usableRules allowCol) = runN RPOAF.lpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (RPOProc MPOAF  usableRules allowCol) = runN RPOAF.mpo  RPOAF.convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))



runRR o = runRpoRuleRemoval o solve

instance ( Info info (RPORuleRemovalProof id)
         , Info info (Problem (Constant (NonDP(MkRewriting strat)) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (RPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id)
   where
    type Typ (RPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id) = NonDP(MkRewriting strat)
    type Trs (RPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id) = NTRS id

    applyO o (RPORuleRemoval LPOAF)   = runRR o RPOAF.rpos convertTyp
    applyO o (RPORuleRemoval LPOSAF ) = runRR o RPOAF.lpos convertTyp
    applyO o (RPORuleRemoval RPOAF)   = runRR o RPOAF.rpo  convertTyp
    applyO o (RPORuleRemoval RPOSAF)  = runRR o RPOAF.rpos convertTyp
