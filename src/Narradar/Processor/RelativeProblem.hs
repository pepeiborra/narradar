{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
module Narradar.Processor.RelativeProblem where

import Data.Monoid

import Narradar.Constraints.Modularity
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types

import qualified Data.Term.Family as Family

-- --------------------------------------------------------------------
-- Convert a relative DP problem into a vanilla DP problem (LOPSTR09)
-- --------------------------------------------------------------------
data RelativeToRegular (info :: * -> *) = RelativeToRegular
type instance InfoConstraint (RelativeToRegular info) = info

data RelativeToRegularProof = RelativeToRegularProof | RelativeToRegularProofFail
          deriving (Eq, Ord, Show)

instance Pretty RelativeToRegularProof where
    pPrint RelativeToRegularProof = text "The two systems form a  Hierarchical Combination" $$
                                    text "and hence the result from LOPSTR09 applies." $$
                                    text "Finiteness of the following DP problem implies relative termination."
    pPrint RelativeToRegularProofFail = text "The two systems do not form a " $$
                                        text "Hierarchical Combination so" $$
                                        text "the result from LOPSTR09 does not apply."

instance ( MkProblem base trs
         , Family.Id trs ~ Id1 t
         , Family.Rule trs ~ Rule t v
         , Ord (t(Term t v)), Ord v, Enum v, Rename v
         , HasId t, Unify t
         , Monoid trs, HasRules trs, HasSignature trs
         , Info info RelativeToRegularProof
         , HasMinimality base
         ) => Processor (RelativeToRegular info) (Problem (Relative trs base) trs) where
  type Typ (RelativeToRegular info) (Problem (Relative trs base) trs) = base
  type Trs (RelativeToRegular info) (Problem (Relative trs base) trs) = trs
  apply RelativeToRegular p@RelativeProblem{relativeTRS}
    | isGeneralizedRelaxedHierarchicalCombination (getR p) relativeTRS
    = let p' = setMinimality A (getBaseProblem p)
      in singleP RelativeToRegularProof p p'

    | otherwise = dontKnow RelativeToRegularProofFail p
