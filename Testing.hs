module Testing where

import Control.Applicative
import Data.AlaCarte
import TRS.FetchRules
import TRS
import System.IO

import Types
import Problem
import NarrowingProblem
import ArgumentFiltering
import DPairs

fullpolicy' :: IO [Rule (T String :+: Var)]
fullpolicy' = do
  contents  <- readFile  "/Users/pepe/fullpolicy.trs"
  let Right trs = parseFile "fn" contents
  return $ trs

fullpolicy = mkTRS <$> fullpolicy'

problem = (solveProblem afProcessor . cycleProcessor . mkNDPProblem) <$> fullpolicy