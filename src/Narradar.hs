{-# LANGUAGE CPP #-}
{-# LANGUAGE PackageImports, NoImplicitPrelude #-}
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
                , module Narradar.GraphTransformation
                , module Narradar.UsableRules
                , module Narradar.ExtraVars
                , module Narradar.NarrowingProblem
                , module Narradar.PrologProblem
                ) where

import Control.Monad
import Data.Maybe
import System.Cmd
import System.Environment
import System.Exit
import System.IO
import System.Posix.Process
import System.Posix.Signals
import System.Console.GetOpt
import Text.Printf

import Prelude -- hiding (Monad(..))
import qualified Prelude as P


import Narradar.Utils
import Narradar.Proof hiding (problem)
import Narradar.GraphViz
import Narradar.Solver
import Narradar.ArgumentFiltering
import Narradar.DPairs
import Narradar.GraphTransformation
import Narradar.UsableRules
import Narradar.ExtraVars
import Narradar.NarrowingProblem
import Narradar.PrologProblem


--main :: IO ()
narradarMain solver = do
#ifndef GHCI
  installHandler sigALRM  (Catch (putStrLn "timeout" >> exitImmediately (ExitFailure (-1)))) Nothing
#endif
  (Options problemFile input diagrams, _, errors) <- getOptions
  sol <- runProofT (solver input)
  putStrLn$ if isSuccess sol then "YES" else "NO"
  when diagrams $ withTempFile "." "narradar.dot" $ \fp h -> do
        hPutStrLn h (pprDot sol)
        hFlush h
        system (printf "dot -Tpdf %s -o %s.pdf " fp problemFile)
        -- hPutStrLn stderr (printf "Log written to %s.pdf" file)
        return ()

-- ------------------------------
-- Command Line Options handling
-- ------------------------------
usage = "Narradar - Automated Narrowing Termination Proofs"

getOptions = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute opts args
  Flags{..} <- foldl (>>=) (return defFlags) actions
  let problemFile = fromMaybe "INPUT" (listToMaybe nonOptions)
  input <- maybe getContents readFile (listToMaybe nonOptions)
  return (Options problemFile input diagramsFlag, nonOptions, errors)

-- data Options where Options :: (TRSC f, Ppr f) => FilePath -> PPT id f Html IO -> Bool -> Options

data Options =  Options { problemFile :: FilePath
                        , input       :: String
                        , diagrams    :: Bool
                        }

data Flags id = Flags { diagramsFlag    :: Bool}

defFlags = Flags{ diagramsFlag     = True}

--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option ""  ["nodiagrams"] (NoArg $ \opts  -> return opts{diagramsFlag = False})                     "Do not produce a pdf proof file"
       , Option "t" ["timeout"] (ReqArg (\arg opts -> scheduleAlarm (read arg) >> return opts) "SECONDS")     "Timeout in seconds (default:none)"
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) >> exitSuccess))         "Displays this help screen"
       ]

-- data NiceSolver where NiceSolver :: (TRSC f, Ppr f) => PPT id f Html IO -> (ProblemProofG id Html f -> String) -> NiceSolver

