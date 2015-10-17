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

module Narradar.Processor.WPO.YicesPipe where

import Control.Monad
import Data.Typeable
import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Constraints.SAT.YicesCircuit as Yices
import Narradar.Constraints.SAT.MonadSAT( IsSimple )
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT

import Narradar.Constraints.SAT.Orderings
import Narradar.Processor.WPO
import qualified Narradar.Constraints.SAT.WPO as WPO
import System.IO.Unsafe

import Debug.Hoed.Observe

solve o = unsafePerformIO . Yices.solveWPO o 1000 MonadSAT.V

-- -------------------
-- WPO SAT Processor
-- -------------------
run o  mkS cTyp p rpo = runWpoReductionPair o solve mkS cTyp rpo p
runRR o = runWpoRuleRemoval o solve

instance ( Info info (WPOReductionPairProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (WPOReductionPair info) (NProblem (MkRewriting strat) id)
   where
    type Typ (WPOReductionPair info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (WPOReductionPair info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (WPOReductionPair LPOAF u) = run o WPO.lpoAF convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair KBOAF u) = run o WPO.kboAF convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair SUM   u) = run o WPO.sum   convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair MAX   u) = run o WPO.max   convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair MPOL  u) = run o WPO.mpol  convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair MSUM  u) = run o WPO.msum  convertTyp (reductionPair (omegaFor u))


instance ( Info info (WPOReductionPairProof id)
         , FrameworkId id, HasArity id
         ) => Processor (WPOReductionPair info) (NProblem (QRewritingN id) id)
   where
    type Typ (WPOReductionPair info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (WPOReductionPair info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (WPOReductionPair LPOAF u) = run o WPO.lpoAF convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair KBOAF u) = run o WPO.kboAF convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair SUM   u) = run o WPO.sum   convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair MAX   u) = run o WPO.max   convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair MPOL  u) = run o WPO.mpol  convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair MSUM  u) = run o WPO.msum  convertTyp1 (reductionPair (omegaFor u))

instance ( Info info (WPORuleRemovalProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (WPORuleRemoval info) (NProblem (MkRewriting strat) id)
   where
    type Typ (WPORuleRemoval info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (WPORuleRemoval info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (WPORuleRemoval POLO) = runRR o WPO.polo convertTyp
    applyO o (WPORuleRemoval LPO ) = runRR o WPO.lpo  convertTyp
    applyO o (WPORuleRemoval KBO ) = runRR o WPO.kbo  convertTyp
    applyO o (WPORuleRemoval TKBO) = runRR o WPO.tkbo convertTyp


instance ( Info info (WPORuleRemovalProof id)
         , FrameworkId id, HasArity id
         ) => Processor (WPORuleRemoval info) (NProblem (QRewritingN id) id)
   where
    type Typ (WPORuleRemoval info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (WPORuleRemoval info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (WPORuleRemoval POLO) = runRR o WPO.polo convertTyp1
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

    applyO o (WPORuleRemoval POLO) = runRR o WPO.polo convertTyp
    applyO o (WPORuleRemoval LPO ) = runRR o WPO.lpo  convertTyp
    applyO o (WPORuleRemoval KBO ) = runRR o WPO.kbo  convertTyp
    applyO o (WPORuleRemoval TKBO) = runRR o WPO.tkbo convertTyp
