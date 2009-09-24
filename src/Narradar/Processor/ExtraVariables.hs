{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module Narradar.Processor.ExtraVariables where

import Data.Foldable (Foldable)

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types
--import Narradar.Types.ArgumentFiltering (bestHeu, mkHeu)
import Narradar.Types.Problem.Relative

data ExtraVarsP  = ExtraVarsP
--data ExtraVarsAF tag =  ExtraVarsAF (MkHeu tag)
data ExtraVarsProof = EVFail | EVAFFail deriving (Eq, Ord, Show)

instance Pretty ExtraVarsProof where
    pPrint EVFail   = text "The TRS contains extra variables."
    pPrint EVAFFail = text "Failed to find an argument filtering which filters out the extra variables"

instance ProofInfo ExtraVarsProof

instance (ExtraVars v trs, Ord v
         ,ProblemInfo (DPProblem Rewriting trs)) =>
          Processor ExtraVarsP (DPProblem Rewriting trs) (DPProblem Rewriting trs)
  where
    apply _ p
       | null (extraVars p) = return p
       | otherwise  = failP EVFail p


instance (ExtraVars v trs, Ord v
         ,ProblemInfo (DPProblem IRewriting trs)) =>
          Processor ExtraVarsP (DPProblem IRewriting trs) (DPProblem IRewriting trs)
  where
    apply _ p
       | null (extraVars p) = return p
       | otherwise  = failP EVFail p


instance (Processor ExtraVarsP (DPProblem base trs) (DPProblem base' trs)) =>
          Processor ExtraVarsP (DPProblem (InitialGoal t base) trs) (DPProblem (InitialGoal t base') trs)
  where
    apply ExtraVarsP p@InitialGoalProblem{..} = updateInitialGoalProblem p `fmap` apply ExtraVarsP baseProblem


instance (Processor ExtraVarsP (DPProblem base trs) (DPProblem base' trs)) =>
          Processor ExtraVarsP (DPProblem (Relative trs base) trs) (DPProblem (Relative trs base') trs)
  where
    apply ExtraVarsP p@RelativeProblem{..} = (\p0' -> p{baseProblem=p0'}) `fmap` apply ExtraVarsP baseProblem


-- In this case we don't need to do anything since Narrowing can terminate with extra variables
instance Processor ExtraVarsP (MkNarrowingGoal id p) (MkNarrowingGoal id p)
  where
    apply ExtraVarsP = return

instance (ExtraVars v trs, Ord v
         ,ProblemInfo (DPProblem Narrowing trs)) =>
         Processor ExtraVarsP (DPProblem Narrowing trs) (DPProblem Narrowing trs) where
    apply _ p
       | null (extraVars p) = return p
       | otherwise  = failP EVFail p

instance (ExtraVars v trs, Ord v
         ,ProblemInfo (DPProblem CNarrowing trs)) =>
         Processor ExtraVarsP (DPProblem CNarrowing trs) (DPProblem CNarrowing trs) where
    apply _ p
       | null (extraVars p) = return p
       | otherwise  = failP EVFail p


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