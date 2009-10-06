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

data RelativeToRegular = RelativeToRegular
data RelativeToRegularProof = RelativeToRegularProof | RelativeToRegularProofFail
          deriving (Eq, Ord, Show)

instance Pretty RelativeToRegularProof where
    pPrint RelativeToRegularProof = text "The two systems form a Generalized Hierarchical Combination" $$
                                    text "and hence the result from LOPSTR09 applies." $$
                                    text "Termination of the following DP problem implies relative termination."
    pPrint RelativeToRegularProofFail = text "The two systems do not form a Generalized" $$
                                        text "Hierarchical Combination and hence we cannot apply" $$
                                        text "the result from LOPSTR09."

instance ( MkProblem base trs
         , SignatureId trs ~ TermId t
         , Ord (t(Term t v)), Ord v, Enum v, HasId t, Match t
         , Monoid trs, HasRules t v trs, HasSignature trs
         , Info info RelativeToRegularProof
         ) => Processor info RelativeToRegular (Problem (Relative trs base) trs) (Problem base trs) where
  apply RelativeToRegular p@RelativeProblem{..}
    | isGeneralizedHierarchicalCombination (getR p) relativeTRS
    = singleP RelativeToRegularProof p (mapR (`mappend` relativeTRS) baseProblem)

    | otherwise = dontKnow RelativeToRegularProofFail p
