{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module Narradar.Processor.ExtraVariables where

import Control.Applicative
import Data.Foldable (Foldable)

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types

data ExtraVarsP  = ExtraVarsP
--data ExtraVarsAF tag =  ExtraVarsAF (MkHeu tag)
data ExtraVarsProof = EVFail | EVAFFail deriving (Eq, Ord, Show)

instance Pretty ExtraVarsProof where
    pPrint EVFail   = text "The TRS contains extra variables."
    pPrint EVAFFail = text "Failed to find an argument filtering which filters out the extra variables"


instance (ExtraVars v trs, Ord v, Info info ExtraVarsProof) =>
          Processor info ExtraVarsP (Problem Rewriting trs) (Problem Rewriting trs)
  where
    apply _ p
       | null (extraVars p) = return p
       | otherwise  = refuted EVFail p


instance (ExtraVars v trs, Ord v, Info info ExtraVarsProof) =>
          Processor info ExtraVarsP (Problem IRewriting trs) (Problem IRewriting trs)
  where
    apply _ p
       | null (extraVars p) = return p
       | otherwise  = refuted EVFail p


instance ( Processor info ExtraVarsP (Problem base trs) (Problem base' trs)
         , Info info ExtraVarsProof
         , Info info (Problem base  trs)
         , Info info (Problem base' trs)
         ) =>
          Processor info ExtraVarsP (Problem (InitialGoal t base) trs) (Problem (InitialGoal t base') trs)
  where
    apply ExtraVarsP p = (`setBaseProblem` p) <$> apply ExtraVarsP (getBaseProblem p)


instance ( Processor info ExtraVarsP (Problem base trs) (Problem base' trs)
         , Info info ExtraVarsProof
         , Info info (Problem base  trs)
         , Info info (Problem base' trs)
         ) =>
          Processor info ExtraVarsP (Problem (Relative trs base) trs) (Problem (Relative trs base') trs)
  where
    apply ExtraVarsP p = (`setBaseProblem` p) <$> apply ExtraVarsP (getBaseProblem p)


-- In this case we don't need to do anything since Narrowing can terminate with extra variables
instance Info info ExtraVarsProof
       => Processor info ExtraVarsP (Problem (MkNarrowingGoal id p) trs) (Problem (MkNarrowingGoal id p) trs)
  where
    apply ExtraVarsP = return

instance (ExtraVars v trs, Ord v, Info info ExtraVarsProof) =>
         Processor info ExtraVarsP (Problem (MkNarrowing a) trs) (Problem (MkNarrowing a) trs) where
    apply ExtraVarsP = return

{-
instance Processor (ExtraVarsAF tag) (NarrowingGoal id p) (NarrowingGoal id p)
    applySearch (ExtraVarsAF mkH) p
       | null vv = return p
       | null orProblems    = failP EVAFFail p
       | otherwise          = orProblems
     where
       vv  = extraVars p
       heu = mkHeu mkH p
-}