{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures, ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

module Narradar.Processor.LOPSTR09 where

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Monad
import Data.Bifunctor
import Data.Monoid
import qualified Data.Set as Set
import Data.Foldable (toList)
import Data.List ((\\))
import Data.Traversable (Traversable)
import Lattice

import Language.Prolog.Representation hiding (addMissingPredicates)

import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Constraints.Syntactic
import Narradar.Types
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF, PolyHeuristic, MkHeu(..),mkHeu)
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGoal as NarrowingGoal
import Narradar.Types.Problem.NarrowingGen as Gen hiding (baseFramework)
import Narradar.Utils
import Narradar.Constraints.VariableCondition
import Narradar.Processor.PrologProblem hiding (SKTransformProof)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF

import Debug.Hoed.Observe

-- ------------------------------------------------------------
-- | This is the processor described at the LOPSTR'09 paper
-- ------------------------------------------------------------
data NarrowingGoalToRelativeRewriting (info :: * -> *) = NarrowingGoalToRelativeRewriting deriving (Eq, Show)
data NarrowingGoalToRelativeRewritingProof = NarrowingGoalToRelativeRewritingProof | NotConstructorBased
           deriving (Eq, Show)

type instance InfoConstraint (NarrowingGoalToRelativeRewriting info) = info

instance Pretty NarrowingGoalToRelativeRewritingProof where
  pPrint NarrowingGoalToRelativeRewritingProof = text "Finiteness of the following relative termination" $$
                                                 text "problem implies the termination of narrowing (LOPSTR'09)"
  pPrint NotConstructorBased = text "The system is not constructor based, and hence the method from (LOPSTR'09) does not apply"


-- | Regular instance. Must be applied before decomposing the problem using the Dependency Graph
instance (gid ~ DPIdentifier (GenId id)
         ,Ord id, Pretty (GenId id)
         ,GetPairs base, Pretty base
         ,Traversable (Problem base)
         ,MkDPProblem (InitialGoal (TermF gid) (MkNarrowingGen base)) (NTRS gid)
         ,NCap base gid
         ,NUsableRules base gid
         ,HasSignature (NProblem base (DPIdentifier id))
--         ,InsertDPairs (Relative (NTRS gid) (InitialGoal (TermF gid) (MkNarrowingGen base))) (NTRS gid)
         ,InsertDPairs base (NTRS gid)
         ,Info info NarrowingGoalToRelativeRewritingProof
         ,Observable base, Observable id
         ) =>
         Processor (NarrowingGoalToRelativeRewriting info) (NProblem (MkNarrowingGoal (DPIdentifier id) base) (DPIdentifier id))
  where
    type Typ (NarrowingGoalToRelativeRewriting info) (NProblem (MkNarrowingGoal (DPIdentifier id) base) (DPIdentifier id)) =
        Relative (NTRS (DPIdentifier (GenId id))) (InitialGoal (TermF (DPIdentifier (GenId id))) (MkNarrowingGen base))
    type Trs (NarrowingGoalToRelativeRewriting info) (NProblem (MkNarrowingGoal (DPIdentifier id) base) (DPIdentifier id)) = NTRS (DPIdentifier (GenId id))
    apply NarrowingGoalToRelativeRewriting prob@NarrowingGoalProblem{goal=Goal goal_f modes}
      | isConstructorBased (getR prob) -- && null (nonLeftLinearRules (getR prob))
      = singleP NarrowingGoalToRelativeRewritingProof prob $
        procLOPSTR09 (getR prob) (getP prob) goal_f modes (getBaseProblemFramework prob)
      | otherwise = dontKnow prob NotConstructorBased


-- | Special instance for InitialGoal Narrowing.
--   We want to be able to apply the dependency graph processor to goal narrowing problems,
--   while still being able to convert them into initial goal rewriting+generators problems.
--   For this we grab the entire dependency graph from the original pairs, which are stored
--   in the InitialGoal problem
instance (gid ~ DPIdentifier (GenId id)
         ,Ord id, Pretty (GenId id)
         ,GetPairs (MkNarrowing base), Pretty (MkNarrowing base)
         ,Traversable (Problem base)
         ,MkDPProblem (InitialGoal (TermF gid) (MkNarrowingGen base)) (NTRS gid)
         ,NCap base gid
         ,NUsableRules base gid
         ,HasSignature (NProblem base (DPIdentifier id))
         ,InsertDPairs (MkNarrowing base) (NTRS gid)
         ,Info info NarrowingGoalToRelativeRewritingProof
         ,FrameworkProblemN base gid
         ,FrameworkProblemN base (DPIdentifier id)
         ) =>
         Processor (NarrowingGoalToRelativeRewriting info) (NProblem (InitialGoal (TermF (DPIdentifier id)) (MkNarrowing base)) (DPIdentifier id))
  where
 type Typ (NarrowingGoalToRelativeRewriting info) (NProblem (InitialGoal (TermF (DPIdentifier id)) (MkNarrowing base)) (DPIdentifier id)) =
     Relative (NTRS (DPIdentifier (GenId id))) (InitialGoal (TermF (DPIdentifier (GenId id))) (MkNarrowingGen base))
 type Trs (NarrowingGoalToRelativeRewriting info) (NProblem (InitialGoal (TermF (DPIdentifier id)) (MkNarrowing base)) (DPIdentifier id)) = NTRS (DPIdentifier (GenId id))
 apply NarrowingGoalToRelativeRewriting prob@InitialGoalProblem{..}
      | isConstructorBased (getR prob) -- && null (nonLeftLinearRules (getR prob))
          = mprod [singleP NarrowingGoalToRelativeRewritingProof prob p | p <- newProblems]
      | otherwise = dontKnow prob NotConstructorBased
  where
   newProblems
      = [mkDerivedDPProblem newFramework
           (insertDPairs (mkDPProblem baseFramework r' p') (tRS goalPairs))
         | (rootSymbol&&&toList -> (Just goal_f,modes)) <- abstract goals

         , let initialRules = [ rule | rule <- rules r'
                                     , let Just id_f = getId (lhs rule)
                                     , id_f == (AnId <$> unmarkDPSymbol goal_f)
                              ]
               goal_vars = Set.fromList [ v | (G,v) <- modes `zip` vars]
               goal'    = Concrete $ term (IdDP GoalId) (return <$> toList goal_vars)
               goalRule = term (IdFunction GoalId) (return <$> toList goal_vars) :->
                          term (AnId <$> unmarkDPSymbol goal_f)
                               (take (length modes) $ map return vars)
               goalPairs = [ l :-> r | l :-> r <- getPairs baseFramework (goalRule:initialRules)
                               , rootSymbol l == Just (IdDP GoalId)]
               r' = mapNarradarTRS convert (getR prob) `mappend` tRS [goalRule]
               p1 = mapNarradarTRS convert (getP prob)
               p' = DPTRS{typ       = Comparable newFramework
                         ,dpsA      = dpsA p1
                         ,rulesUsed = rulesUsed p1 `mappend` tRS [goalRule]
                         ,depGraph  = depGraph p1
                         ,unifiers  = unifiers p1
                         ,sig       = sig p1}

               dg = mkDGraph' baseFramework r'
                              (insertDPairs' baseFramework
                                             (mapNarradarTRS convert (pairs dgraph))
                                             goalPairs)
                              [goal']
               newFramework = relative genRules $
                              InitialGoal [goal'] (Just dg) $
                              NarrowingGen (getBaseFramework baseFramework)
        ]

   baseFramework = getBaseProblemFramework prob

   genRules = tRS [ genTerm :-> term (AnId <$> c) (replicate ar genTerm)
                           | c <- toList $ getConstructorSymbols (getR prob)
                           , let ar = getArity prob c]

   genTerm   = term (IdFunction GenId) []

   vars = [toEnum 0 ..] \\ toList (getVars prob)
   convert  = mapTermSymbols (fmap AnId)


procLOPSTR09 :: (gid ~ DPIdentifier (GenId id)
                ,Ord id, Pretty (GenId id)
                ,GetPairs base, Pretty base
                ,Traversable (Problem base)
                ,MkDPProblem (InitialGoal (TermF gid) (MkNarrowingGen base)) (NTRS gid)
                ,NCap base gid
                ,NUsableRules base gid
                ,HasSignature (NProblem base (DPIdentifier id))
                ,InsertDPairs base (NTRS gid)
                ,Observable base, Observable id
                ) =>
                NTRS (DPIdentifier id) -> NTRS (DPIdentifier id) -> DPIdentifier id -> [Mode] -> base ->
                NProblem (Relative (NTRS gid) (InitialGoal (TermF gid) (MkNarrowingGen base))) gid
procLOPSTR09 rr pp goal_f modes baseFramework
   = mkDerivedDPProblem newType
                        (insertDPairs (mkDPProblem baseFramework r' p')
                                      (mkTRS [ l :-> r | l :-> r <- getPairs newType (goalRule:initialRules)
                                             , rootSymbol l == Just (IdDP GoalId)]))
  where
       newType  = relative genRules $ initialGoal [Concrete goal'] $ NarrowingGen baseFramework

       r'       = mapNarradarTRS convert rr `mappend` mkTRS [goalRule]
       p'       = mapNarradarTRS convert pp

       initialRules = [ rule | rule <- rules r'
                             , let Just id_f = getId (lhs rule)
                             , id_f == (AnId <$> unmarkDPSymbol goal_f)
                      ]

       goal'    = term (IdDP GoalId)       (return <$> toList goal_vars)
       goalRule = term (IdFunction GoalId) (return <$> toList goal_vars) :->
                  term (AnId <$> unmarkDPSymbol goal_f)
                       (take (length modes) [ if var `Set.member` goal_vars
                                               then return var
                                               else genTerm
                                             | var <- vars])

       genRules = tRS [ genTerm :-> term (AnId <$> c) (replicate ar genTerm)
                           | c <- toList $ getConstructorSymbols rr
                           , let ar = getArity rr c]

       genTerm   = term (IdFunction GenId) []
       goal_vars = Set.fromList [ v | (G,v) <- modes `zip` vars]
       vars = [toEnum 0 ..] \\ toList (getVars rr)
       convert  = mapTermSymbols (fmap AnId)


-- ------------------------------------------------------
-- | Transforms a Prolog problem into a Narrowing problem
-- ------------------------------------------------------

data SKTransform (info :: * -> *) = SKTransform
type instance InfoConstraint (SKTransform info) = info

instance Info info SKTransformProof => Processor (SKTransform info) PrologProblem
 where
  type Typ (SKTransform info) PrologProblem = InitialGoal (TermF DRP) Narrowing
  type Trs (SKTransform info) PrologProblem = NTRS DRP
  apply SKTransform p0@PrologProblem{..} =
   andP SKTransformProof p0
     [ mkNewProblem (initialGoal [Abstract the_goal] narrowing) sk_rr
         | let sk_rr = prologTRS'' rr (getSignature rr)
               rr    = skTransformWith id (prepareProgram $ addMissingPredicates program)
         , goal    <- goals
         , let Goal id mm = skTransformGoal goal
         , let the_goal = term (IdDP id) (map return mm)
     ]


data SKTransformProof = SKTransformProof
  deriving (Eq, Show)

instance Pretty SKTransformProof where
  pPrint SKTransformProof
      = text "Transformed into an initial goal narrowing problem" $$
        text "(Schneider-Kamp transformation)"

data SKTransformInf heu (info :: * -> *) = SKTransformInf (MkHeu heu)
type instance InfoConstraint (SKTransformInf heu info) = info

instance (Info info SKTransformProof, PolyHeuristic heu DRP) => Processor (SKTransformInf heu info) PrologProblem
 where
  type Typ (SKTransformInf heu info) PrologProblem = Infinitary DRP Rewriting
  type Trs (SKTransformInf heu info) PrologProblem = NTRS DRP
  apply (SKTransformInf heu) p0@PrologProblem{..} =
   andP SKTransformProof p0 =<< sequence
     [  msum (map return probs)
         | goal    <- goals
         , let probs = mkDerivedInfinitaryProblem (bimap IdDP id $ skTransformGoal goal) heu (mkNewProblem rewriting sk_p)
     ]
    where
       sk_p = prologTRS'' rr (getSignature rr)
       rr   = skTransformWith id (prepareProgram $ addMissingPredicates program)
