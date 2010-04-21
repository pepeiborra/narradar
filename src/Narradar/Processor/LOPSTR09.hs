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
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGoal as NarrowingGoal
import Narradar.Types.Problem.NarrowingGen as Gen
import Narradar.Utils
import Narradar.Constraints.VariableCondition
import Narradar.Processor.PrologProblem hiding (SKTransformProof)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF

instance Pretty SKTransformProof where
  pPrint SKTransformProof
      = text "Transformed into an initial goal narrowing problem" $$
        text "(Schneider-Kamp transformation)"

-- ------------------------------------------------------------
-- | This is the processor described at the LOPSTR'09 paper
-- ------------------------------------------------------------
data NarrowingGoalToRelativeRewriting = NarrowingGoalToRelativeRewriting deriving (Eq, Show)
data NarrowingGoalToRelativeRewritingProof = NarrowingGoalToRelativeRewritingProof | NotConstructorBased
           deriving (Eq, Show)

instance Pretty NarrowingGoalToRelativeRewritingProof where
  pPrint NarrowingGoalToRelativeRewritingProof = text "Finiteness of the following relative termination" $$
                                                 text "problem implies the termination of narrowing (LOPSTR'09)"
  pPrint NotConstructorBased = text "The system is not constructor based, and hence the method from (LOPSTR'09) does not apply"


instance (gid ~ DPIdentifier (GenId id)
         ,Ord id, Pretty (GenId id)
         ,GetPairs base
         ,Traversable (Problem base), MkDPProblem base (NTRS gid), Pretty base
         ,NCap base gid
         ,NUsableRules base gid
         ,HasSignature (NProblem base (DPIdentifier id)), DPIdentifier id ~ SignatureId (NProblem base (DPIdentifier id))
--         ,InsertDPairs (Relative (NTRS gid) (InitialGoal (TermF gid) (MkNarrowingGen base))) (NTRS gid)
         ,InsertDPairs base (NTRS gid)
         ,Info info NarrowingGoalToRelativeRewritingProof
         ) =>
         Processor info NarrowingGoalToRelativeRewriting
                        (NProblem (MkNarrowingGoal (DPIdentifier id) base) (DPIdentifier id))
                        (NProblem (Relative (NTRS gid) (InitialGoal (TermF gid)
                                                                    (MkNarrowingGen base)))
                                  gid)
  where
    apply NarrowingGoalToRelativeRewriting prob@NarrowingGoalProblem{goal=Goal goal_f modes, ..}
      | isConstructorBased (getR prob) =
            singleP NarrowingGoalToRelativeRewritingProof prob prob'
      | otherwise = dontKnow prob NotConstructorBased
     where
{-
       prob'    = insertDPairs (mkDPProblem newType r' p')
                               (mkTRS [ l :-> r | l :-> r <- getPairs newType (goalRule:initialRules)
                                                , rootSymbol l == Just (IdDP GoalId)])
-}
       prob'    = mkDerivedDPProblem newType
                               (insertDPairs (mkDPProblem baseType r' p')
                                             (mkTRS [ l :-> r | l :-> r <- getPairs newType (goalRule:initialRules)
                                                              , rootSymbol l == Just (IdDP GoalId)]))

       baseType = getProblemType baseProblem
       newType  = relative genRules $ initialGoal [goal'] $ NarrowingGen baseType

       r'       = mapNarradarTRS convert (getR prob) `mappend` mkTRS [goalRule]
       p'       = mapNarradarTRS convert (getP prob)

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
                           | c <- toList $ getConstructorSymbols (getR prob)
                           , let ar = getArity prob c]

       genTerm   = term (IdFunction GenId) []
       goal_vars = Set.fromList [ v | (G,v) <- modes `zip` vars]
       vars = [toEnum 0 ..] \\ toList (getVars prob)
       convert  = mapTermSymbols (fmap AnId)


-- --------------------------------------------------------------------------------
-- | Transforms a Prolog termination problem into a Narrowing termination problem
-- --------------------------------------------------------------------------------

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

-- -------------------------------------------------------------------------
-- Transforms a narrowing problem into a rewriting problem (FLOPS'08 Vidal)
-- -------------------------------------------------------------------------
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
