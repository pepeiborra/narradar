{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module Narradar.Processor.RelativeProblemIPL14 (RelativeToRegularIPL14(..)) where

import Data.List ((\\), partition)
import Data.Monoid
import Data.Typeable
import Prelude.Extras
import qualified Data.Set as Set

import Narradar.Constraints.Modularity
import Narradar.Constraints.Syntactic
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types hiding (goals)
import Narradar.Types.Problem.InitialGoal

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe

-- --------------------------------------------------------------------
-- Convert a relative DP problem into a vanilla DP problem (LOPSTR09)
-- --------------------------------------------------------------------
data RelativeToRegularIPL14 (info :: * -> *) = RelativeToRegularIPL14
type instance InfoConstraint (RelativeToRegularIPL14 info) = info

data RelativeToRegularProofIPL14 =
    RelativeToRegularProof
  | RelativeToGoalDirectedProof
  | RelativeToRegularProofFail RelativeToRegularFailReasonIPL14
          deriving (Eq, Ord, Show, Typeable, Generic)

data RelativeToRegularFailReasonIPL14 =
    NoHC
  | HCbutNotNonDuplicatingOrHT
  | HTbutNotInitialGoal
  | GoalNotHT
  deriving (Eq,Ord,Show, Generic)

instance Observable RelativeToRegularProofIPL14
instance Observable RelativeToRegularFailReasonIPL14

instance Pretty RelativeToRegularProofIPL14 where
    pPrint RelativeToRegularProof = text "The two systems form a Hierarchical Combination," $$
                                    text "and the base is non duplicating." $$
                                    text "Hence the result from IPL14 applies." $$
                                    text "Finiteness of the following DP problem implies relative termination."
    pPrint RelativeToGoalDirectedProof =

      text "The two systems form a Hierarchical Combination," $$
      text "the extension is right HT, and the goal is HT as well." $$
      text "Hence the result of IPL14 applies, and finiteness of the following" $$
      text "goal-directed DP problem implies relative termination."
    pPrint (RelativeToRegularProofFail NoHC) = text "The two systems do not form a " $$
                                               text "Hierarchical Combination so" $$
                                               text "the result from IPL14 does not apply."
    pPrint (RelativeToRegularProofFail HCbutNotNonDuplicatingOrHT) =
      text "The two systems form a Hierarchical Combination," $$
      text "but the base is duplicating and the extension is not right-RT."
    pPrint (RelativeToRegularProofFail HTbutNotInitialGoal) =
      text "The two systems form a Hierarchical Combination but" $$
      text "the base is duplicating. Termination is only provable" $$
      text "for initial terms from the extension. Try again specifying" $$
      text "an initial goal strategy."
    pPrint (RelativeToRegularProofFail GoalNotHT) =
      text "The two systems form a Hierarchical Combination and the extension is right-HT," $$
      text "but the goal is not HT"

instance ( FrameworkProblem base trs
         , GetPairs base
         , trs ~ NTRS (DPIdentifier id)
         , Ord id
         , Info info RelativeToRegularProofIPL14
         ) => Processor (RelativeToRegularIPL14 info) (Problem (Relative trs base) trs)
 where
  type Typ (RelativeToRegularIPL14 info) (Problem (Relative trs base) trs) = base
  type Trs (RelativeToRegularIPL14 info) (Problem (Relative trs base) trs) = trs
  applyO _ RelativeToRegularIPL14 p@RelativeProblem{relativeTRS}
    = let p' = mkDPProblem b
                           (getR p `mappend` relativeTRS)
                           (tRS $ getPairs b ex')
      in singleP RelativeToRegularProof p p'

    where
     b = getBaseProblemFramework p
     (ex, base) = makeHierarchicalCombination (rules $ getR p) (rules relativeTRS)
     duplicatingSymbols = Set.fromList $ map (getId . lhs) $ duplicatingRules base
     (dup, _base') = partition ((`Set.member` duplicatingSymbols) . getId . lhs)
                              (rules base)
     ex' = dup `mappend` ex

instance ( MkProblem base trs
         , Family.Id trs ~ Family.Id t
         , Family.Rule trs ~ Rule t v
         , Ord1 t, Ord v, Enum v, Rename v
         , HasId1 t, Unify t, Ord(Family.Id t)
         , Monoid trs, HasRules trs, HasSignature trs
         , Info info RelativeToRegularProofIPL14
         , HasMinimality base
         ) => Processor (RelativeToRegularIPL14 info)
                        (Problem (Relative trs (InitialGoal t base)) trs) where
  type Typ (RelativeToRegularIPL14 info) (Problem (Relative trs (InitialGoal t base)) trs) = InitialGoal t base
  type Trs (RelativeToRegularIPL14 info) (Problem (Relative trs (InitialGoal t base)) trs) = trs
  applyO _ RelativeToRegularIPL14 p@RelativeProblem{relativeTRS}
    | isHierarchicalCombination ex relativeTRS
    , isNonDuplicatingTRS relativeTRS
    =  let p' = setMinimality A (getBaseProblem p)
       in singleP RelativeToRegularProof p p'

    | isHierarchicalCombination ex relativeTRS
    , isHTtrs ex relativeTRS
    , goals <- concrete $ goals $ getBaseProblem p
    , all (isHT (getSignature ex) (getSignature relativeTRS)) goals
    = let p' = setMinimality A (getBaseProblem p)
      in singleP RelativeToGoalDirectedProof p p'

    | isHierarchicalCombination ex relativeTRS
    = dontKnow (RelativeToRegularProofFail HCbutNotNonDuplicatingOrHT) p

    | otherwise = dontKnow (RelativeToRegularProofFail NoHC) p

    where
     ex = rules(getR p) \\ rules relativeTRS
