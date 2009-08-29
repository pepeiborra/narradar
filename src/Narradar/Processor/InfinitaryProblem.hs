{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Narradar.Processor.InfinitaryProblem where

import Control.Applicative
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.Ppr

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristicN, HeuristicN, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types as Narradar
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Utils
import Lattice



data InfinitaryToRewriting heu = InfinitaryToRewriting (MkHeu heu)
data NarrowingGoalToInfinitary = NarrowingGoalToInfinitary


-- This is the infinitary constructor rewriting AF processor described in
-- "Termination of Logic Programs ..." (Schneider-Kamp et al)
instance (PolyHeuristicN heu id, Lattice (AF_ id), Ord id, Ppr id) =>
    Processor (InfinitaryToRewriting heu) (NarradarTRS id Var) (Infinitary id Rewriting) Rewriting where
  applySearch (InfinitaryToRewriting mk) p
    | null orProblems = [failP InfinitaryToRewritingFail p]
    | otherwise = orProblems
   where
     orProblems = do
       let (Infinitary af _) = getProblemType p
           heu = mkHeu mk p
       af' <-  Set.toList $ invariantEV heu p af
       let p' = mkNewProblem Rewriting (iUsableRules p (rhs <$> rules (getP p)))
       return $ singleP (InfinitaryToRewritingProof af') p (AF.apply af' p')

instance (p ~ DPProblem (NarrowingGoalGen id typ) trs
         ,Ord id, Ppr id, ProblemInfo p, IsDPProblem typ) =>
    Processor NarrowingGoalToInfinitary trs (NarrowingGoalGen id typ) (Infinitary id typ) where
    apply _ p@(getProblemType -> NarrowingGoal pi p0) = singleP NarrowingGoalToInfinitaryProof p $ mkNewProblem (Infinitary pi p0) p

-- -------------
-- Proofs
-- -------------

data InfinitaryToRewritingProof id where
    InfinitaryToRewritingProof :: AF_ id -> InfinitaryToRewritingProof id
    InfinitaryToRewritingFail  :: InfinitaryToRewritingProof ()

instance Ppr id => Ppr (InfinitaryToRewritingProof id) where
    ppr InfinitaryToRewritingFail = text "Failed to find an argument filtering that satisfies" <>
                                         text "the variable condition."
    ppr (InfinitaryToRewritingProof af) = text "Termination of the following rewriting DP problem" <+>
                                               text "implies termination of the original problem." $$
                                               text "The argument filtering used is:" $$
                                               ppr af
instance Ppr id => ProofInfo (InfinitaryToRewritingProof id)

data NarrowingGoalToInfinitaryProof = NarrowingGoalToInfinitaryProof deriving (Eq, Ord, Show)

instance Ppr NarrowingGoalToInfinitaryProof where
 ppr _ = text "Termination of this infinitary rewriting problem" $$
         text "implies termination of the original problem"

instance ProofInfo NarrowingGoalToInfinitaryProof