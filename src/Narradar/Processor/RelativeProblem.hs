{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Narradar.Processor.RelativeProblem (RegularImpliesRelative(..)) where

import Data.Monoid
import Data.Typeable

import Narradar.Constraints.Modularity
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types
import Narradar.Types.Problem.Relative

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe

-- --------------------------------------------------------------------
-- Convert a relative DP problem into a vanilla DP problem (LOPSTR09)
-- --------------------------------------------------------------------
data RelativeToRegular (info :: * -> *) = RelativeToRegular
type instance InfoConstraint (RelativeToRegular info) = info

data RelativeToRegularProof = RelativeToRegularProof | RelativeToRegularProofFail
          deriving (Eq, Ord, Show, Typeable, Generic)

instance Observable RelativeToRegularProof

instance Pretty RelativeToRegularProof where
    pPrint RelativeToRegularProof = text "The two systems form a  Hierarchical Combination" $$
                                    text "and hence the result from LOPSTR09 applies." $$
                                    text "Finiteness of the following DP problem implies relative termination."
    pPrint RelativeToRegularProofFail = text "The two systems do not form a " $$
                                        text "Hierarchical Combination so" $$
                                        text "the result from LOPSTR09 does not apply."
{-

 THIS PROCESSOR IS UNSOUND UNLESS THE BASE IS NON-DUPLICATING, AND EVEN THAT IS ONlY A CONJECTURE AT THIS POINT.
 USE THE IPL14 PROCESSOR INSTEAD

instance ( FrameworkProblem base trs
         , Family.Id trs ~ Family.Id t
         , Family.Rule trs ~ Rule t v
         , Info info RelativeToRegularProof
         ) => Processor (RelativeToRegular info) (Problem (Relative trs base) trs) where
  type Typ (RelativeToRegular info) (Problem (Relative trs base) trs) = base
  type Trs (RelativeToRegular info) (Problem (Relative trs base) trs) = trs
  applyO _ RelativeToRegular p@RelativeProblem{relativeTRS}
    | isGeneralizedRelaxedHierarchicalCombination (getR p) relativeTRS
    = let p' = setMinimality A (getBaseProblem p)
      in singleP RelativeToRegularProof p p'

    | otherwise = dontKnow RelativeToRegularProofFail p
-}

data RegularImpliesRelative (info :: * -> *) = RegularImpliesRelative deriving (Eq, Show, Ord, Generic, Typeable)
data RegularImpliesRelativeProof = RegularImpliesRelativeProof deriving (Eq, Show, Ord, Generic, Typeable)

type instance InfoConstraint (RegularImpliesRelative info) = info

instance Observable (RegularImpliesRelative info)
instance Observable (RegularImpliesRelativeProof)

instance Pretty (RegularImpliesRelativeProof) where
  pPrint _ = text "Regular termination implies relative termination"

instance (Info info RegularImpliesRelativeProof
         ,GetPairs base, HasRules trs
         ,FrameworkProblem base trs
         ,trs ~ NTRS (DPIdentifier id)
         ,Ord id
         ) =>
         Processor (RegularImpliesRelative info) (Problem (Relative trs base) trs) where
 type Typ (RegularImpliesRelative info) (Problem (Relative trs base) trs) = base
 type Trs (RegularImpliesRelative info) (Problem (Relative trs base) trs) = trs

 applyO o _ p = singleP RegularImpliesRelativeProof p p' where
   p'  = mkDPProblemO o typ rr' (tRS $ getPairs typ rr')
   rr' = tRS $ rules(getR p) ++ rules(getR $ baseProblem p)
   typ = getFramework $ baseProblem p
