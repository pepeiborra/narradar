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

module Narradar.Processor.RPO.Z3 where

import Control.Monad
import Control.DeepSeq
import Narradar.Types as Narradar hiding (Var)
import Narradar.Constraints.SAT.MonadSAT( IsSimple )
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT

import Narradar.Constraints.SAT.Orderings
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Processor.RPO
import System.IO.Unsafe

import Narradar.Constraints.SAT.Z3Circuit

import Debug.Hoed.Observe

solve :: ( Hashable id, Hashable v, Pretty id, NFData v, Show id, Show v, Ord id, Ord v, Enum v, Bounded v
         ) => Observer -> Narradar.Constraints.SAT.Z3Circuit.Z3MRPO id v (MonadSAT.EvalM v a) -> Maybe a
solve o x = unsafePerformIO $ do
  res <- solveRPO "RPO" o minBound x
  return res

-- -------------------
-- RPO SAT Processor
-- -------------------
--run :: (MonadSAT.Decode (Data.Var.Family.Var a) Bool, MkDPProblem typ1 (NF NTRSConstraint NarradarTRS_ (Term (TermF (Usable a)) Narradar.Types.Var.Var)), MkDPProblem typ (NarradarTRS (TermF (Data.Id.Family.Id a)) Narradar.Types.Var.Var), RemovePrologId (Data.Id.Family.Id a), Hashable (Data.Var.Family.Var a), Hashable id, Data.Suitable.Suitable info (RPOProof (Data.Id.Family.Id a)), Data.Suitable.Suitable info (Problem typ (NarradarTRS (TermF (Data.Id.Family.Id a)) Narradar.Types.Var.Var)), Pretty (Data.Id.Family.Id a), Pretty id, HasSignature (Problem typ (NF NTRSConstraint NarradarTRS_ (Term (TermF (Data.Id.Family.Id a)) Narradar.Types.Var.Var))), Prelude.Extras.Ord1 info, Control.DeepSeq.NFData (Data.Var.Family.Var a), Control.DeepSeq.NFData (Data.Id.Family.Id a), Control.Applicative.Applicative info, Data.Typeable.Internal.Typeable (Data.Id.Family.Id a), Data.Typeable.Internal.Typeable typ, Data.Typeable.Internal.Typeable info, Show (Data.Var.Family.Var a), Show (Data.Id.Family.Id a), Show id, Ord (Problem typ (NarradarTRS (TermF (Data.Id.Family.Id a)) Narradar.Types.Var.Var)), Ord (Data.Var.Family.Var a), Ord (Data.Id.Family.Id a), Ord id, Ord a, Monad m, Enum (Data.Var.Family.Var a), Bounded (Data.Var.Family.Var a),

-- Narradar.Constraints.SAT.Usable.SymbolRes a ~ Funsat.TermCircuit.RPO.Symbols.SymbolRes (Data.Id.Family.Id a)

-- ) => Observer -> Narradar.Constraints.SAT.Usable.MkSATSymbol RPOAF.EnvRPO (Usable a) -> ((Data.Id.Family.Id a -> Usable a) -> typ -> typ1) -> (Problem typ1 (NF NTRSConstraint NarradarTRS_ (Term (TermF (Usable a)) Narradar.Types.Var.Var)) -> Narradar.Constraints.SAT.Z3Circuit.Z3M Narradar.Constraints.SAT.Z3Circuit.RPOCircuit id (Data.Var.Family.Var a) (MonadSAT.EvalM (Data.Var.Family.Var a) ([Int], [MonadSAT.Tree (Term (TermF (Usable a)) Narradar.Types.Var.Var) MonadSAT.Var]))) -> Problem typ (NarradarTRS (TermF (Data.Id.Family.Id a)) Narradar.Types.Var.Var) -> Proof info m (Problem typ (NarradarTRS (TermF (Data.Id.Family.Id a)) Narradar.Types.Var.Var))
run  o mkS cTyp p rpo = runRpoProc  o solve mkS cTyp rpo p
runN o mkS cTyp p rpo = runRpoProcN o solve mkS cTyp rpo p

instance ( Info info (RPOProof id)
         , Info info (Problem (Constant (MkRewriting strat) (TermF id)) (NTRS id))
         , FrameworkId id
         , FrameworkTyp (MkRewriting strat), Observable strat
         ) => Processor (RPOProc info) (NProblem (MkRewriting strat) id)
   where
    type Typ (RPOProc info) (NProblem (MkRewriting strat) id) = MkRewriting strat
    type Trs (RPOProc info) (NProblem (MkRewriting strat) id) = NTRS id
    applyO o (RPOProc RPOSAF usablerules allowCol) = run o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOSAF usablerules allowCol) = run o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc RPOAF  usablerules allowCol) = run o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOAF  usablerules allowCol) = run o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc MPOAF  usablerules allowCol) = run o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (RPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (RPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    applyO o (RPOProc RPOSAF usablerules allowCol) = run o RPOAF.rpos convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOSAF usablerules allowCol) = run o RPOAF.lpos convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc RPOAF  usablerules allowCol) = run o RPOAF.rpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc LPOAF  usablerules allowCol) = run o RPOAF.lpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))
    applyO o (RPOProc MPOAF  usablerules allowCol) = run o RPOAF.mpo  convertTyp1 (setupAF allowCol >=> reductionPair (omegaFor usablerules))

instance (Info info (RPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id, IsSimple id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO o (RPOProc RPOSAF _ allowCol) = run o RPOAF.rpos convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc LPOSAF _ allowCol) = run o RPOAF.lpos convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc RPOAF  _ allowCol) = run o RPOAF.lpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc LPOAF  _ allowCol) = run o RPOAF.rpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))
    applyO o (RPOProc MPOAF  _ allowCol) = run o RPOAF.mpo  convertTypIG (setupAF allowCol >=> reductionPairIG ((,return[]).omegaIG))

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
    applyO o (RPOProc RPOSAF usableRules allowCol) = liftProblem (run o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOSAF usableRules allowCol) = liftProblem (run o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc RPOAF  usableRules allowCol) = liftProblem (run o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOAF  usableRules allowCol) = liftProblem (run o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc MPOAF  usableRules allowCol) = liftProblem (run o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))

instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id

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
    applyO o (RPOProc RPOSAF usableRules allowCol) = liftProblem (run o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOSAF usableRules allowCol) = liftProblem (run o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc RPOAF  usableRules allowCol) = liftProblem (run o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc LPOAF  usableRules allowCol) = liftProblem (run o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))
    applyO o (RPOProc MPOAF  usableRules allowCol) = liftProblem (run o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPair (omegaFor usableRules)))


instance (Info info (RPOProof id)
         ,FrameworkId id
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO o (RPOProc RPOSAF usableRules allowCol) = runN o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOSAF usableRules allowCol) = runN o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc RPOAF  usableRules allowCol) = runN o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOAF  usableRules allowCol) = runN o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc MPOAF  usableRules allowCol) = runN o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

instance (FrameworkId  id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enabled, but not tested
    applyO o (RPOProc RPOSAF usableRules allowCol) = runN o RPOAF.rpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOSAF usableRules allowCol) = runN o RPOAF.lpos convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc RPOAF  usableRules allowCol) = runN o RPOAF.rpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc LPOAF  usableRules allowCol) = runN o RPOAF.lpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))
    applyO o (RPOProc MPOAF  usableRules allowCol) = runN o RPOAF.mpo  convertTyp (setupAF allowCol >=> reductionPairN (omegaFor usableRules))

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
