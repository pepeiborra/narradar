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

module Narradar.Processor.WPO.SBV where

import Control.Monad
import qualified Control.Exception as CE
import Data.Char (toLower)
import Data.Typeable
import System.Directory
import System.IO.Unsafe
import System.Environment

import Narradar.Utils
import Narradar.Types as Narradar hiding (Var)
import Narradar.Constraints.SAT.MonadSAT( IsSimple )
import Narradar.Constraints.SAT.Orderings
import qualified Narradar.Constraints.SAT.WPO as WPO
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Processor.WPO
import System.IO.Unsafe

import Narradar.Constraints.SAT.SBVCircuit (solveWPO)
import Data.SBV (z3,yices,defaultSMTCfg,sbvAvailableSolvers,SMTConfig(..))

import Debug.Hoed.Observe


solve alg o x = unsafePerformIO $ do
  env :: Either CE.SomeException String
      <- CE.try(getEnv "SMT_SOLVER")
  tmp <- getTemporaryDirectory
  all <- sbvAvailableSolvers
  withTempFile tmp "sbv.smt" $ \fp h -> do
    let cfg = case fmap(map toLower) env of
               Right "yices" -> [yices]
               Right "z3"    -> [z3]
               Right "all"   -> all
               _ -> [defaultSMTCfg]
        cfg' = if debugging then [ c{smtFile = Just fp} | c <- cfg ] else cfg
    when debugging $ putStrLn ("Saving SMT output in " ++ fp)
    res <- solveWPO alg o minBound cfg x
    return (not debugging, res)

-- -------------------
-- WPO SAT Processor
-- -------------------
run o alg mkS cTyp rpo = runWpoReductionPair o alg (solve alg) mkS cTyp rpo
runRR o = runWpoRuleRemoval o (solve "polo")

instance ( Info info (WPOReductionPairProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id, HasArity id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (WPOReductionPair info) (NProblem (MkRewriting strat) id)
   where
    type Typ (WPOReductionPair info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (WPOReductionPair info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (WPOReductionPair alg@LPOAF u) = run o alg WPO.lpoAF convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@KBOAF u) = run o alg WPO.kboAF convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@SUM   u) = run o alg WPO.sum   convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MAX   u) = run o alg WPO.max   convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@(MPOL x y)  u) = run o alg (WPO.mpol_xy x y)  convertTyp (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MSUM  u) = run o alg WPO.msum  convertTyp (reductionPair (omegaFor u))


instance ( Info info (WPOReductionPairProof id)
         , FrameworkId id, HasArity id
         ) => Processor (WPOReductionPair info) (NProblem (QRewritingN id) id)
   where
    type Typ (WPOReductionPair info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (WPOReductionPair info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (WPOReductionPair alg@LPOAF u) = run o alg WPO.lpoAF convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@KBOAF u) = run o alg WPO.kboAF convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@SUM   u) = run o alg WPO.sum   convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MAX   u) = run o alg WPO.max   convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@(MPOL x y)  u) = run o alg (WPO.mpol_xy x y)  convertTyp1 (reductionPair (omegaFor u))
    applyO o (WPOReductionPair alg@MSUM  u) = run o alg WPO.msum  convertTyp1 (reductionPair (omegaFor u))

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
