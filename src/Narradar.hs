{-# LANGUAGE CPP #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module Narradar ( narradarMain
                , module Narradar.Solver
                , module Narradar.ArgumentFiltering
                , module Narradar.DPairs
                , module Narradar.ReductionPair
                , module Narradar.GraphTransformation
                , module Narradar.UsableRules
                , module Narradar.ExtraVars
                , module Narradar.NarrowingProblem
                , module Narradar.PrologProblem
                , module Narradar.Types
                , module Control.Monad.MonadPlus.Parameterized
                ) where

import Control.Monad
import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Data.Maybe
import System.Cmd
import System.Environment
import System.Exit
import System.IO
import System.Posix.Process
import System.Posix.Signals
import System.Console.GetOpt
import Text.Printf

import Prelude as P

import Narradar.Utils
import Narradar.Proof hiding (problem)
import Narradar.GraphViz
import Narradar.Solver hiding ( prologSolver, prologSolver'
                              , narradarSolver, narradarSolver'
                              , narrowingSolver )
import Narradar.ArgumentFiltering (Heuristic(..), simpleHeu, simpleHeu', typeHeu, typeHeu2, bestHeu, innermost, outermost)
import Narradar.DPairs
import Narradar.GraphTransformation
import Narradar.UsableRules
import Narradar.ReductionPair
import Narradar.ExtraVars
import Narradar.NarrowingProblem
import Narradar.PrologProblem
import Narradar.Types
import Narradar.Convert


--main :: IO ()
narradarMain solver = do
  (Options problemFile input diagrams, _, errors) <- getOptions
  sol <- runProofT (solver input)
  putStrLn$ if isSuccess sol then "YES" else "NO"
  when diagrams $ withTempFile "." "narradar.dot" $ \fp h -> do
        let sol' = if isSuccess sol then simplify sol else sol
        hPutStrLn h (pprDot sol')
        hFlush h
#ifdef DEBUG
        writeFile (problemFile ++ ".dot") (pprDot sol')
#endif
--        system (printf "dot -Tpdf %s -o %s.pdf " fp problemFile)
        -- hPutStrLn stderr (printf "Log written to %s.pdf" file)
        P.return ()

-- ------------------------------
-- Command Line Options handling
-- ------------------------------
usage = "Narradar - Automated Narrowing Termination Proofs"

getOptions = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute opts args
  Flags{..} <- foldl (P.>>=) (P.return defFlags) actions
  let problemFile = fromMaybe "INPUT" (listToMaybe nonOptions)
  input <- maybe getContents readFile (listToMaybe nonOptions)
  P.return (Options problemFile input diagramsFlag, nonOptions, errors)

-- data Options where Options :: (TRSC f, Ppr f) => FilePath -> PPT id f Html IO -> Bool -> Options

data Options =  Options { problemFile :: FilePath
                        , input       :: String
                        , diagrams    :: Bool
                        }

data Flags id = Flags { diagramsFlag    :: Bool}

defFlags = Flags{ diagramsFlag     = True}

--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option ""  ["nodiagrams"] (NoArg $ \opts  -> P.return opts{diagramsFlag = False})                     "Do not produce a pdf proof file"
#ifndef GHCI
       , Option "t" ["timeout"] (ReqArg setTimeout "SECONDS")     "Timeout in seconds (default:none)"
#endif
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) P.>> exitSuccess))         "Displays this help screen"
       ]

-- data NiceSolver where NiceSolver :: (TRSC f, Ppr f) => PPT id f Html IO -> (ProblemProofG id Html f -> String) -> NiceSolver

setTimeout arg opts = do
  scheduleAlarm (read arg)
  installHandler sigALRM  (Catch (putStrLn "timeout" P.>> exitImmediately (ExitFailure (-1)))) Nothing
  P.return opts
