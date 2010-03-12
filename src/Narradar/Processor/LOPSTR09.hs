{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Narradar.Processor.LOPSTR09 where

import Control.Applicative
import Control.Monad
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Lattice

import Language.Prolog.Representation hiding (addMissingPredicates)

import Narradar.Constraints.VariableCondition
import Narradar.Framework
import Narradar.Types
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF, PolyHeuristic, MkHeu(..),mkHeu)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.Problem.NarrowingGoal as NarrowingGoal
import Narradar.Processor.PrologProblem hiding (SKTransformProof)

instance Pretty SKTransformProof where
  pPrint SKTransformProof
      = text "Transformed into an initial goal narrowing problem" $$
        text "(Schneider-Kamp transformation)"


-- SK Transform
-- ------------

data SKTransform = SKTransform
instance Info info SKTransformProof =>
         Processor info SKTransform
                   PrologProblem {- ==> -} (NProblem (NarrowingGoal DRP) DRP)
 where
  apply SKTransform p0@PrologProblem{..} =
   andP SKTransformProof p0
     [ mkNewProblem (narrowingGoal the_goal) sk_p
         | let sk_p = prologTRS'' rr (getSignature rr)
               rr   = skTransformWith id (prepareProgram $ addMissingPredicates program)
         , goal    <- goals
         , let the_goal = -- (IdFunction <$> skTransformGoal goal) `mappend`
                          (IdDP       <$> skTransformGoal goal)
     ]
data SKTransformProof = SKTransformProof
  deriving (Eq, Show)

data SKTransformInf heu = SKTransformInf (MkHeu heu)
instance (Info info SKTransformProof
         ,PolyHeuristic heu DRP
         ) =>
         Processor info (SKTransformInf heu)
                   PrologProblem {- ==> -} (NProblem (Infinitary DRP Rewriting) DRP)
 where
  apply (SKTransformInf heu) p0@PrologProblem{..} =
   andP SKTransformProof p0 =<< sequence
     [  msum (map return probs)
         | goal    <- goals
         , let probs = mkDerivedInfinitaryProblem (IdDP <$> skTransformGoal goal) heu (mkNewProblem rewriting sk_p)
     ]
    where
       sk_p = prologTRS'' rr (getSignature rr)
       rr   = skTransformWith id (prepareProgram $ addMissingPredicates program)


-- Solving narrowing as infinitary problems (FLOPS'08)
-- ---------------------------------------------------
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
           base_p = getProblemType (getBaseProblem p)
       af' <- Set.toList $ invariantEV heu p (NarrowingGoal.pi p)
       let p' = mkDerivedDPProblem base_p p
       return $ singleP (NarrowingGoalToRewritingProof af') p (AF.apply af' p')

data NarrowingGoalToRewritingProof id where
    NarrowingGoalToRewritingProof :: AF_ id -> NarrowingGoalToRewritingProof id
    NarrowingGoalToRewritingFail  :: NarrowingGoalToRewritingProof id
instance Pretty id => Pretty (NarrowingGoalToRewritingProof id) where
    pPrint NarrowingGoalToRewritingFail = text "Failed to find a safe argument filtering"

    pPrint (NarrowingGoalToRewritingProof af) = text "Termination of the following rewriting DP problem implies" <+>
                                               text "termination of the original problem [FLOPS08]." $$
                                               text "The argument filtering used is:" $$
                                               pPrint af
