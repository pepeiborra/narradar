{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}

module Narradar.Processor.InfinitaryProblem where

import Control.Applicative
import Data.Traversable (Traversable)
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.Ppr

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristic, Heuristic, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types as Narradar
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Utils
import Lattice



data InfinitaryToRewriting heu = InfinitaryToRewriting (MkHeu heu)
data NarrowingGoalToInfinitary = NarrowingGoalToInfinitary


-- | This is the infinitary constructor rewriting AF processor described in
--   "Termination of Logic Programs ..." (Schneider-Kamp et al)
instance (PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,Info info (InfinitaryToRewritingProof id)
         ) =>
    Processor info (InfinitaryToRewriting heu)
              (DPProblem (Infinitary id Rewriting) (NTRS id Var))
              (DPProblem Rewriting (NTRS id Var))
  where
  applySearch (InfinitaryToRewriting mk) p
    | null orProblems = [failP (InfinitaryToRewritingFail :: InfinitaryToRewritingProof id) p]
    | otherwise = orProblems
   where
     orProblems = do
       let (Infinitary af _) = getProblemType p
           heu = mkHeu mk p
       af' <-  Set.toList $ invariantEV heu p af
       let p' = mkDerivedProblem Rewriting (iUsableRules p (rhs <$> rules (getP p)))
       return $ singleP (InfinitaryToRewritingProof af') p (AF.apply af' p')


-- | This is the infinitary constructor rewriting AF processor described in
--   "Termination of Logic Programs ..." (Schneider-Kamp et al)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id Var
         ,ICap t v (typ, trs), IUsableRules t v (typ,trs)
         ,PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,MkDPProblem typ (NTRS id Var), Traversable (DPProblem typ)
         ,Info info (InfinitaryToRewritingProof id)
         ) =>
    Processor info (InfinitaryToRewriting heu)
              (DPProblem (Infinitary id typ) (NTRS id Var))
              (DPProblem typ (NTRS id Var))
  where
  applySearch (InfinitaryToRewriting mk) p
    | null orProblems = [failP (InfinitaryToRewritingFail :: InfinitaryToRewritingProof id) p]
    | otherwise = orProblems
   where
     orProblems = do
       let (Infinitary af base_p) = getProblemType p
           heu = mkHeu mk p
       af' <-  Set.toList $ invariantEV heu p af
       let p' = mkDerivedProblem base_p (iUsableRules p (rhs <$> rules (getP p)))
       return $ singleP (InfinitaryToRewritingProof af') p (AF.apply af' p')



instance ( Ord id, Pretty id, MkDPProblem typ (NTRS id Var), Pretty typ, HTMLClass (MkNarrowingGoal id typ)
         , Info info NarrowingGoalToInfinitaryProof
         ) =>
    Processor info NarrowingGoalToInfinitary
                  (DPProblem (MkNarrowingGoal id typ) (NTRS id Var))
                  (DPProblem (Infinitary id typ) (NTRS id Var))
   where
    apply _ p@(getProblemType -> NarrowingGoal pi p0) = singleP NarrowingGoalToInfinitaryProof p $ mkDerivedProblem (Infinitary pi p0) p

-- -------------
-- Proofs
-- -------------

data InfinitaryToRewritingProof id where
    InfinitaryToRewritingProof :: AF_ id -> InfinitaryToRewritingProof id
    InfinitaryToRewritingFail  :: InfinitaryToRewritingProof id

instance Pretty id => Pretty (InfinitaryToRewritingProof id) where
    pPrint InfinitaryToRewritingFail = text "Failed to find an argument filtering that satisfies" <>
                                         text "the variable condition."
    pPrint (InfinitaryToRewritingProof af) = text "Termination of the following rewriting DP problem" <+>
                                               text "implies termination of the original problem." $$
                                               text "The argument filtering used is:" $$
                                               pPrint af

data NarrowingGoalToInfinitaryProof = NarrowingGoalToInfinitaryProof deriving (Eq, Ord, Show)

instance Pretty NarrowingGoalToInfinitaryProof where
 pPrint _ = text "Termination of this infinitary rewriting problem" $$
         text "implies termination of the original problem"
