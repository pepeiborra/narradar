module Testing where

import Types
import Data.AlaCarte
import TRS.FetchRules
import System.IO
--import NarrowingProblem
import ArgumentFiltering

fullpolicy :: IO (TRS (IdFunctions :+*: IdDPs) (T IdFunctions :+: T IdDPs :+: Var))
fullpolicy = do
  contents  <- readFile  "/Users/pepe/fullpolicy.trs"
  let Right trs = parseFile "fn" contents
  return $ TRS trs