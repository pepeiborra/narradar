module Main where

import System.Environment
import System.Exit
import System.IO
import Text.Printf
import Text.XHtml

import TRS.FetchRules
import Types
import Solver


main = do
  args <- getArgs
  case args of
    [file] -> do
              contents <- readFile file
              case parseFile file contents of
                Left error -> print error >> exitWith (ExitFailure 1)
                Right trs_ -> do
                  sol <- solveNarrowing $ mkTRS trs_
                  putStr (renderHtml sol)
    _ -> getProgName >>= \n -> printf "Narradar - Automated Narrowing Termination Proofs\n USAGE: %s <system.trs>" n