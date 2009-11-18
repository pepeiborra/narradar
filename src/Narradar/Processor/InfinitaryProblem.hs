{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}

module Narradar.Processor.InfinitaryProblem where

import Control.Applicative
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.Ppr

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF, PolyHeuristic, Heuristic, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types as Narradar
import Narradar.Types.Problem.Infinitary as Infinitary
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Utils
import Lattice
import Prelude hiding (pi)

data InfinitaryToRewriting heu = InfinitaryToRewriting (MkHeu heu) Bool
data NarrowingGoalToInfinitary heu = NarrowingGoalToInfinitary (MkHeu heu) Bool

infinitaryToRewriting heu = apply(InfinitaryToRewriting heu False)
narrowingGoalToInfinitary heu = apply(NarrowingGoalToInfinitary heu False)

-- | This is the infinitary constructor rewriting AF processor described in
--   "Termination of Logic Programs ..." (Schneider-Kamp et al)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id
         ,HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         ,PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,MkDPProblem typ (NTRS id), Traversable (Problem typ)
         ,ApplyAF (NProblem typ id)
         ,Info info (InfinitaryToRewritingProof id)
         ,ICap t v (typ, trs)
         ,IUsableRules t v typ trs
         ) =>
    Processor info (InfinitaryToRewriting heu)
              (NProblem (Infinitary id typ) id)
              (NProblem typ id)
  where
  applySearch (InfinitaryToRewriting mk usable) p
    | null orProblems = [dontKnow (InfinitaryToRewritingFail :: InfinitaryToRewritingProof id) p]
    | otherwise = orProblems
   where
     orProblems = do
       let heu    = mkHeu mk p
           base_p = getProblemType (Infinitary.baseProblem p)
       af' <-  Set.toList $ invariantEV heu p (Infinitary.pi p)
       let p' = mkDerivedProblem base_p $
                if usable then iUsableRules p (rhs <$> rules (getP p)) else p
       return $ singleP (InfinitaryToRewritingProof af') p (AF.apply af' p')



instance ( Ord id, Pretty id, MkDPProblem typ (NTRS id), Pretty typ, HTMLClass (MkNarrowingGoal id typ)
         , HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         , Lattice (AF_ id)
         , PolyHeuristic heu id
         , Foldable (Problem typ)
         , Info info NarrowingGoalToInfinitaryProof
         , NCap id (typ, NTRS id)
         , NUsableRules typ id
         ) =>
    Processor info (NarrowingGoalToInfinitary heu)
                   (NProblem (MkNarrowingGoal id typ) id)
                   (NProblem (Infinitary id typ) id)
   where
    applySearch (NarrowingGoalToInfinitary mk usable) p@(getProblemType -> NarrowingGoal _ pi p0) = do
        pi' <- Set.toList $ invariantEV heu p pi
        let p' = mkDerivedProblem (infinitary' pi' p0) p
        return $ singleP NarrowingGoalToInfinitaryProof p p'
     where
      heu = mkHeu mk p

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
