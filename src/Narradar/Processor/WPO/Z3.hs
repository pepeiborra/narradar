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

module Narradar.Processor.WPO.Z3 where

import Control.Monad
import Narradar.Types as Narradar hiding (Var)
import Narradar.Constraints.SAT.MonadSAT( IsSimple )
import Narradar.Constraints.SAT.Orderings
import qualified Narradar.Constraints.SAT.WPO as WPO
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Processor.WPO
import System.IO.Unsafe

import qualified Narradar.Constraints.SAT.Z3Circuit as Z3

import Debug.Hoed.Observe

solve = Z3.solveWPO minBound

-- -------------------
-- WPO SAT Processor
-- -------------------
run  mkS cTyp p rpo = runWpoProc  (unsafePerformIO . solve) mkS cTyp rpo p
runPOL = run WPO.pol convertTyp (reductionPair omegaNone)
--runN mkS cTyp p rpo = runWpoProcN (unsafePerformIO . solve) mkS cTyp rpo p

instance ( Info info (WPOProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (WPOProc info) (NProblem (MkRewriting strat) id)
   where
    type Typ (WPOProc info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (WPOProc info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO _ (WPOProc POL u) = run WPO.pol convertTyp (reductionPair (omegaFor u))
{-
instance (FrameworkId id
         ,Info info (WPOProof id)
         ) => Processor (WPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (WPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (WPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    applyO _ (WPOProc WPOSAF usablerules allowCol) = run WPOAF.rpos convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (WPOProc LPOSAF usablerules allowCol) = run WPOAF.lpos convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (WPOProc WPOAF  usablerules allowCol) = run WPOAF.rpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (WPOProc LPOAF  usablerules allowCol) = run WPOAF.lpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO _ (WPOProc MPOAF  usablerules allowCol) = run WPOAF.mpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (Info info (WPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id, IsSimple id
         ) => Processor (WPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (WPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (WPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO _ (WPOProc WPOSAF _ allowCol) = run WPOAF.rpos convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (WPOProc LPOSAF _ allowCol) = run WPOAF.lpos convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (WPOProc WPOAF  _ allowCol) = run WPOAF.lpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (WPOProc LPOAF  _ allowCol) = run WPOAF.rpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO _ (WPOProc MPOAF  _ allowCol) = run WPOAF.mpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))

instance (Info info (WPOProof id)
         ,Info info (NProblem IRewriting id)
         ,Info info (Problem (Constant IRewriting (TermF id)) (NTRS id))
         ,FrameworkProblemN IRewriting id
--         ,FrameworkProblemN (Constant IRewriting (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) IRewriting) id
         ) => Processor (WPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    type Typ (WPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = InitialGoal (TermF id) IRewriting
    type Trs (WPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = NTRS id
    applyO _ (WPOProc WPOSAF usableRules allowCol) = liftProblem (run WPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc LPOSAF usableRules allowCol) = liftProblem (run WPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc WPOAF  usableRules allowCol) = liftProblem (run WPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc LPOAF  usableRules allowCol) = liftProblem (run WPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc MPOAF  usableRules allowCol) = liftProblem (run WPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))

instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (WPOProof id)
         ) => Processor (WPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (WPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (WPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    applyO _ (WPOProc WPOSAF _ allowCol) = run WPOAF.rpos convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (WPOProc LPOSAF _ allowCol) = run WPOAF.lpos convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (WPOProc WPOAF  _ allowCol) = run WPOAF.lpo  convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (WPOProc LPOAF  _ allowCol) = run WPOAF.rpo  convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)
    applyO _ (WPOProc MPOAF  _ allowCol) = run WPOAF.mpo  convertTypIG (setupAF allowCol >=> reductionPairIG omegaIGgen)

instance (Info info (WPOProof id)
         ,Info info (NProblem INarrowingGen id)
         ,Info info (Problem (Constant INarrowingGen (TermF id)) (NTRS id))
         ,FrameworkProblemN INarrowingGen id
--         ,FrameworkProblemN (Constant INarrowingGen (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) INarrowingGen) id
         ,GenSymbol id
         ) => Processor (WPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id)
   where
    type Typ (WPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = InitialGoal (TermF id) INarrowingGen
    type Trs (WPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = NTRS id
    applyO _ (WPOProc WPOSAF usableRules allowCol) = liftProblem (run WPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc LPOSAF usableRules allowCol) = liftProblem (run WPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc WPOAF  usableRules allowCol) = liftProblem (run WPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc LPOAF  usableRules allowCol) = liftProblem (run WPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO _ (WPOProc MPOAF  usableRules allowCol) = liftProblem (run WPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))


instance (Info info (WPOProof id)
         ,FrameworkId id
         ) => Processor (WPOProc info) (NProblem Narrowing id)
  where
    type Typ (WPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (WPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO _ (WPOProc WPOSAF usableRules allowCol) = runN WPOAF.rpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc LPOSAF usableRules allowCol) = runN WPOAF.lpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc WPOAF  usableRules allowCol) = runN WPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc LPOAF  usableRules allowCol) = runN WPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc MPOAF  usableRules allowCol) = runN WPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

instance (FrameworkId  id
         ,Info info (WPOProof id)
         ) => Processor (WPOProc info) (NProblem CNarrowing id)
  where
    type Typ (WPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (WPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO _ (WPOProc WPOSAF usableRules allowCol) = runN WPOAF.rpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc LPOSAF usableRules allowCol) = runN WPOAF.lpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc WPOAF  usableRules allowCol) = runN WPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc LPOAF  usableRules allowCol) = runN WPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO _ (WPOProc MPOAF  usableRules allowCol) = runN WPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

-}
