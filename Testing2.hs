module Testing where

import Control.Applicative
import Data.AlaCarte
import TRS.FetchRules
import TRS
import System.IO

--import Types
--import NarrowingProblem
--import ArgumentFiltering

fullpolicy' :: IO [Rule (T :+: Var)]
fullpolicy' = do
  contents  <- readFile  "/Users/pepe/fullpolicy.trs"
  let Right trs = parseFile "fn" contents
  return $ trs

--fullpolicy = mkTRS <$> fullpolicy'