{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
module Narradar.Processor.RelativeProblem where

import Data.Monoid

import Narradar.Constraints.Modularity
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types

-- --------------------------------------------------------------------
-- Convert a relative DP problem into a vanilla DP problem (LOPSTR09)
-- --------------------------------------------------------------------
data RelativeToRegular = RelativeToRegular
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
         , SignatureId trs ~ TermId t
         , Ord (t(Term t v)), Ord v, Enum v, Rename v
         , HasId t, Unify t
         , Monoid trs, HasRules t v trs, HasSignature trs
         , Info info RelativeToRegularProof
         , HasMinimality base
         ) => Processor info RelativeToRegular (Problem (Relative trs base) trs) (Problem base trs) where
  apply RelativeToRegular p@RelativeProblem{..}
    | isGeneralizedRelaxedHierarchicalCombination (getR p) relativeTRS
    = let p' = setMinimality A baseProblem
      in singleP RelativeToRegularProof p p'

    | otherwise = dontKnow RelativeToRegularProofFail p
