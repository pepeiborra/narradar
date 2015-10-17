{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
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

module Narradar.Processor.RPO.SBV where

import Control.DeepSeq
import Control.Monad
import qualified Control.Exception as CE
import Data.Char (toLower)
import System.IO.Unsafe
import System.Environment

import Narradar.Types as Narradar hiding (Var)
import Narradar.Constraints.SAT.MonadSAT( IsSimple )
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Constraints.SAT.Orderings
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Processor.RPO

import Narradar.Constraints.SAT.SBVCircuit
import Data.SBV (z3,yices,defaultSMTCfg,sbvAvailableSolvers)

import Debug.Hoed.Observe

solve :: (Hashable id, Hashable v, Pretty id, NFData v, Show id, Show v, Ord id, Ord v, Enum v, Bounded v
         ,Observable a, Observable v
         ) => Observer -> RPOM id v (MonadSAT.EvalM v a) -> Maybe a
solve o@(O _ oo) x = unsafePerformIO $ do
  env :: Either CE.SomeException String
      <- CE.try(getEnv "SMT_SOLVER")
  all <- sbvAvailableSolvers
  let cfg = case fmap(map toLower) env of
               Right "yices" -> [yices]
               Right "z3"    -> [z3]
               Right "all"   -> all
               _ -> [defaultSMTCfg]
  oo "solveRPO" (solveRPO "rpo") minBound cfg x

-- -------------------
-- RPO SAT Processor
-- -------------------
run  o mkS cTyp p rpo = let ?observer = o in runRpoProc  o solve mkS cTyp rpo p
runN o mkS cTyp p rpo = let ?observer = o in runRpoProcN o solve mkS cTyp rpo p

instance ( Info info (RPOProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (RPOProc info) (NProblem (MkRewriting strat) id)
   where
    type Typ (RPOProc info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (RPOProc info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (RPOProc RPOSAF usablerules allowCol) = let ?observer = o in run o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOSAF usablerules allowCol) = let ?observer = o in run o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc RPOAF  usablerules allowCol) = let ?observer = o in run o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOAF  usablerules allowCol) = let ?observer = o in run o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc MPOAF  usablerules allowCol) = let ?observer = o in run o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (RPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (RPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (RPOProc RPOSAF usablerules allowCol) = let ?observer = o in run o RPOAF.rpos convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOSAF usablerules allowCol) = let ?observer = o in run o RPOAF.lpos convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc RPOAF  usablerules allowCol) = let ?observer = o in run o RPOAF.rpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOAF  usablerules allowCol) = let ?observer = o in run o RPOAF.lpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc MPOAF  usablerules allowCol) = let ?observer = o in run o RPOAF.mpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (Info info (RPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id, IsSimple id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO o (RPOProc RPOSAF _ allowCol) = let ?observer = o in run o RPOAF.rpos convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc LPOSAF _ allowCol) = let ?observer = o in run o RPOAF.lpos convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc RPOAF  _ allowCol) = let ?observer = o in run o RPOAF.lpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc LPOAF  _ allowCol) = let ?observer = o in run o RPOAF.rpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc MPOAF  _ allowCol) = let ?observer = o in run o RPOAF.mpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))

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
    applyO o (RPOProc RPOSAF usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOSAF usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc RPOAF  usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOAF  usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc MPOAF  usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))

instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    applyO o (RPOProc RPOSAF _ allowCol) = let ?observer = o in run o RPOAF.rpos convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO o (RPOProc LPOSAF _ allowCol) = let ?observer = o in run o RPOAF.lpos convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO o (RPOProc RPOAF  _ allowCol) = let ?observer = o in run o RPOAF.lpo  convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO o (RPOProc LPOAF  _ allowCol) = let ?observer = o in run o RPOAF.rpo  convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO o (RPOProc MPOAF  _ allowCol) = let ?observer = o in run o RPOAF.mpo  convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)

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
    applyO o (RPOProc RPOSAF usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOSAF usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc RPOAF  usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOAF  usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc MPOAF  usableRules allowCol) = liftProblem (let ?observer = o in run o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))


instance (Info info (RPOProof id)
         ,FrameworkId id
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO o (RPOProc RPOSAF usableRules allowCol) = let ?observer = o in runN o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOSAF usableRules allowCol) = let ?observer = o in runN o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc RPOAF  usableRules allowCol) = let ?observer = o in runN o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOAF  usableRules allowCol) = let ?observer = o in runN o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc MPOAF  usableRules allowCol) = let ?observer = o in runN o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

instance (FrameworkId  id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO o (RPOProc RPOSAF usableRules allowCol) = let ?observer = o in runN o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOSAF usableRules allowCol) = let ?observer = o in runN o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc RPOAF  usableRules allowCol) = let ?observer = o in runN o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOAF  usableRules allowCol) = let ?observer = o in runN o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc MPOAF  usableRules allowCol) = let ?observer = o in runN o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

runRR o = runRpoRuleRemoval o solve

instance ( Info info (RPORuleRemovalProof id)
         , Info info (Problem (Constant (NonDP(MkRewriting strat)) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat)
         , Observable strat, Observable (SomeInfo info)
         ) => Processor (RPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id)
   where
    type Typ (RPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id) = NonDP(MkRewriting strat)
    type Trs (RPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id) = NTRS id

    applyO o (RPORuleRemoval LPOAF)   = let ?observer = o in runRR o RPOAF.rpos convertTyp
    applyO o (RPORuleRemoval LPOSAF ) = let ?observer = o in runRR o RPOAF.lpos convertTyp
    applyO o (RPORuleRemoval RPOAF)   = let ?observer = o in runRR o RPOAF.rpo  convertTyp
    applyO o (RPORuleRemoval RPOSAF)  = let ?observer = o in runRR o RPOAF.rpos convertTyp
