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
import Data.Typeable
import Narradar.Types as Narradar hiding (Var)
import Narradar.Constraints.SAT.MonadSAT( IsSimple )
import Narradar.Constraints.SAT.Orderings
import qualified Narradar.Constraints.SAT.WPO as WPO
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Processor.WPO
import System.IO.Unsafe

import qualified Narradar.Constraints.SAT.Z3Circuit as Z3

import Debug.Hoed.Observe

solve msg o = unsafePerformIO . Z3.solveWPO msg o minBound

-- -------------------
-- WPO SAT Processor
-- -------------------
run o alg mkS cTyp rpo = runWpoReductionPair o alg (solve alg) mkS cTyp rpo
runRR o = runWpoRuleRemoval o (solve "POLO")

--runN mkS cTyp p rpo = runWpoProcN (unsafePerformIO . solve) mkS cTyp rpo p

instance ( Info info (WPOReductionPairProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (WPOReductionPair info) (NProblem (MkRewriting strat) id)
   where
    type Typ (WPOReductionPair info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (WPOReductionPair info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (WPOReductionPair alg@(MPOL x y) u) = run o alg (WPO.mpol_xy x y) convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MSUM  u) = run o alg WPO.msum  convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MAX   u) = run o alg WPO.max   convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@SUM   u) = run o alg WPO.sum   convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@LPOAF u) = run o alg WPO.lpoAF convertTyp (reductionPair (omegaFor u))

instance (FrameworkId id
         ,Info info (WPOReductionPairProof id)
         ) => Processor (WPOReductionPair info) (NProblem (QRewritingN id) id)
   where
    type Typ (WPOReductionPair info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (WPOReductionPair info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (WPOReductionPair alg@(MPOL x y) u) = run o alg (WPO.mpol_xy x y) convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MSUM  u) = run o alg WPO.msum convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MAX   u) = run o alg WPO.max  convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@SUM   u) = run o alg WPO.sum  convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@LPOAF u)= run o alg WPO.lpoAF convertTyp1 (reductionPair (omegaFor u))
{-
instance (Info info (WPOReductionPairProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id, IsSimple id
         ) => Processor (WPOReductionPair info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (WPOReductionPair info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (WPOReductionPair info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO o (WPOReductionPair MPOL u) = run o WPO.mpol convertTypIG (reductionPairIG ((,return[]).omegaIG))
    applyO o (WPOReductionPair MSUM u) = run o WPO.msum convertTypIG (reductionPairIG ((,return[]).omegaIG))
    applyO o (WPOReductionPair MAX  u) = run o WPO.sum  convertTypIG (reductionPairIG ((,return[]).omegaIG))
    applyO o (WPOReductionPair LPOAF  u) = run o WPO.max  convertTypIG (reductionPairIG ((,return[]).omegaIG))
    applyO o (WPOReductionPair SUM  u) = run o WPO.lpoAF  convertTypIG (reductionPairIG ((,return[]).omegaIG))

instance (Info info (WPOReductionPairProof id)
         ,Info info (NProblem IRewriting id)
         ,Info info (Problem (Constant IRewriting (TermF id)) (NTRS id))
         ,FrameworkProblemN IRewriting id
--         ,FrameworkProblemN (Constant IRewriting (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) IRewriting) id
         ) => Processor (WPOReductionPair info) (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    type Typ (WPOReductionPair info) (NProblem (InitialGoal (TermF id) IRewriting) id) = InitialGoal (TermF id) IRewriting
    type Trs (WPOReductionPair info) (NProblem (InitialGoal (TermF id) IRewriting) id) = NTRS id
    applyO o (WPOReductionPair MPOL u) = liftProblem (run o WPO.mpol convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair MSUM u) = liftProblem (run o WPO.msum convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair MAX  u) = liftProblem (run o WPO.max  convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair LPOAF  u) = liftProblem (run o WPO.lpoAF  convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair SUM  u) = liftProblem (run o WPO.sum  convertTyp (reductionPair (omegaFor u)))

instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (WPOReductionPairProof id)
         ) => Processor (WPOReductionPair info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (WPOReductionPair info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (WPOReductionPair info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    applyO o (WPOReductionPair MPOL _ ) = run o WPO.mpol convertTypIG (reductionPairIG omegaIGgen)
    applyO o (WPOReductionPair MSUM _ ) = run o WPO.msum convertTypIG (reductionPairIG omegaIGgen)
    applyO o (WPOReductionPair MAX  _ ) = run o WPO.max  convertTypIG (reductionPairIG omegaIGgen)
    applyO o (WPOReductionPair LPOAF _) = run o WPO.lpoAF  convertTypIG (reductionPairIG omegaIGgen)
    applyO o (WPOReductionPair SUM  _ ) = run o WPO.sum  convertTypIG (reductionPairIG omegaIGgen)

instance (Info info (WPOReductionPairProof id)
         ,Info info (NProblem INarrowingGen id)
         ,Info info (Problem (Constant INarrowingGen (TermF id)) (NTRS id))
         ,FrameworkProblemN INarrowingGen id
--         ,FrameworkProblemN (Constant INarrowingGen (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) INarrowingGen) id
         ,GenSymbol id
         ) => Processor (WPOReductionPair info) (NProblem (InitialGoal (TermF id) INarrowingGen) id)
   where
    type Typ (WPOReductionPair info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = InitialGoal (TermF id) INarrowingGen
    type Trs (WPOReductionPair info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = NTRS id
    applyO o (WPOReductionPair MPOL u) = liftProblem (run o WPO.mpol convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair MSUM u) = liftProblem (run o WPO.msum convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair MAX  u) = liftProblem (run o WPO.max  convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair LPOAF  u) = liftProblem (run o WPO.lpoAF  convertTyp (reductionPair (omegaFor u)))
    applyO o (WPOReductionPair SUM  u) = liftProblem (run o WPO.sum  convertTyp (reductionPair (omegaFor u)))
-}


instance ( Info info (WPORuleRemovalProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (WPORuleRemoval info) (NProblem (MkRewriting strat) id)
   where
    type Typ (WPORuleRemoval info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (WPORuleRemoval info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (WPORuleRemoval (POLO x y)) = runRR o (WPO.polo_xy x y) convertTyp
    applyO o (WPORuleRemoval LPO ) = runRR o WPO.lpo  convertTyp
    applyO o (WPORuleRemoval KBO ) = runRR o WPO.kbo  convertTyp
    applyO o (WPORuleRemoval TKBO) = runRR o WPO.tkbo convertTyp


instance ( Info info (WPORuleRemovalProof id)
         , FrameworkId id, HasArity id
         ) => Processor (WPORuleRemoval info) (NProblem (QRewritingN id) id)
   where
    type Typ (WPORuleRemoval info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (WPORuleRemoval info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (WPORuleRemoval (POLO x y)) = runRR o (WPO.polo_xy x y) convertTyp1
    applyO o (WPORuleRemoval LPO ) = runRR o WPO.lpo  convertTyp1
    applyO o (WPORuleRemoval KBO ) = runRR o WPO.kbo  convertTyp1
    applyO o (WPORuleRemoval TKBO) = runRR o WPO.tkbo convertTyp1

instance ( Info info (WPORuleRemovalProof id)
         , Info info (Problem (Constant (NonDP(MkRewriting strat)) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat, Typeable strat
         ) => Processor (WPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id)
   where
    type Typ (WPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id) = NonDP(MkRewriting strat)
    type Trs (WPORuleRemoval info) (NProblem (NonDP(MkRewriting strat)) id) = NTRS id

    applyO o (WPORuleRemoval (POLO x y)) = runRR o (WPO.polo_xy x y) convertTyp
    applyO o (WPORuleRemoval LPO ) = runRR o WPO.lpo  convertTyp
    applyO o (WPORuleRemoval KBO ) = runRR o WPO.kbo  convertTyp
    applyO o (WPORuleRemoval TKBO) = runRR o WPO.tkbo convertTyp
