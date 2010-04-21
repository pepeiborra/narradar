{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}

module Narradar.Processor.FLOPS08 where

import Control.Applicative
import Control.Monad
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.Ppr

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF, PolyHeuristic, Heuristic, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types as Narradar
import Narradar.Types.Problem.NarrowingGoal as NarrowingGoal
import Narradar.Utils
import Lattice
import Prelude hiding (pi)



instance Pretty id => Pretty (NarrowingGoalToRewritingProof id) where
    pPrint NarrowingGoalToRewritingFail = text "Failed to find a safe argument filtering"

    pPrint (NarrowingGoalToRewritingProof af) = text "Termination of the following rewriting DP problem implies" <+>
                                               text "termination of the original problem [FLOPS08]." $$
                                               text "The argument filtering used is:" $$
                                               pPrint af

data ComputeSafeAF heu = ComputeSafeAF (MkHeu heu)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id
         ,HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         ,ICap t v (typ, trs), IUsableRules t v typ trs
         ,PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,MkDPProblem typ (NTRS id), Foldable (Problem typ)
         ,ApplyAF (NProblem typ id)
         ,Info info (NarrowingGoalToRewritingProof id)
         ) =>
    Processor info (ComputeSafeAF heu)
              (NProblem (MkNarrowingGoal id typ) id)
              (NProblem (MkNarrowingGoal id typ) id)
  where
  applySearch (ComputeSafeAF mk) p
    | null orProblems = [dontKnow (NarrowingGoalToRewritingFail :: NarrowingGoalToRewritingProof id) p]
    | otherwise = map return orProblems
   where
     orProblems = do
       let heu = mkHeu mk p
       af' <-  Set.toList $ invariantEV heu p (NarrowingGoal.pi p)
       return p{pi=af'}

data NarrowingGoalToRewriting heu = NarrowingGoalToRewriting (MkHeu heu)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id
         ,HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         ,ICap t v (typ, trs), IUsableRules t v typ trs
         ,PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,MkDPProblem typ (NTRS id), Traversable (Problem typ)
         ,ApplyAF (NProblem typ id)
         ,Info info (NarrowingGoalToRewritingProof id)
         ) =>
    Processor info (NarrowingGoalToRewriting heu)
              (NProblem (MkNarrowingGoal id typ) id)
              (NProblem typ id)
  where
  applySearch (NarrowingGoalToRewriting mk) p
    | null orProblems = [dontKnow (NarrowingGoalToRewritingFail :: NarrowingGoalToRewritingProof id) p]
    | otherwise = orProblems
   where
     orProblems = do
       let heu = mkHeu mk p
           base_p = getFramework (getBaseProblem p)
       af' <-  Set.toList $ invariantEV heu p (NarrowingGoal.pi p)
       let p' = mkDerivedDPProblem base_p p
       return $ singleP (NarrowingGoalToRewritingProof af') p (AF.apply af' p')

data NarrowingGoalToRewritingProof id where
    NarrowingGoalToRewritingProof :: AF_ id -> NarrowingGoalToRewritingProof id
    NarrowingGoalToRewritingFail  :: NarrowingGoalToRewritingProof id
