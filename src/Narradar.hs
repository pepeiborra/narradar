{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}

module Narradar ( narradarMain, Options(..), defOpts
                , module Narradar.Solver
                , module Narradar.Processor.Graph
                , module Narradar.Processor.ReductionPair
                , module Narradar.Processor.GraphTransformation
                , module Narradar.Processor.UsableRules
                , module Narradar.Processor.NarrowingProblem
                , module Narradar.Processor.PrologProblem
                , module Narradar.Types
                ) where


import Control.Monad.Free
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

import Narradar.Types hiding (note, dropNote)
import Narradar.Utils
import Narradar.Framework.Proof hiding (problem)
import Narradar.Framework.GraphViz
import Narradar.Solver hiding ( prologSolver, prologSolver'
                              , narradarSolver, narradarSolver'
                              , narrowingSolver )

import Narradar.Types.DPairs
import Narradar.Processor.Graph
import Narradar.Processor.GraphTransformation
import Narradar.Processor.UsableRules
import Narradar.Processor.ReductionPair
import Narradar.Processor.NarrowingProblem
import Narradar.Processor.PrologProblem
import Narradar.Utils.Convert


--main :: IO ()
narradarMain solver = do
  (flags@Options{..}, _, _errors) <- getOptions
  ~(yes, sol, log) <- (solver flags input)
  when (verbose > 0) (  hSetBuffering stdout NoBuffering P.>> putStrLn log)
  putStrLn$ if yes then "YES" else "NO"
  when (verbose>0 && yes) $ print $ pprProof sol
  when (diagrams && (yes || verbose > 0)) $ withTempFile "." "narradar.dot" $ \fp h -> do
        hPutStrLn h (pprDot' PprDot{showFailedPaths = verbose > 1} sol)
        hFlush h
#ifdef DEBUG
        when (verbose > 1) $ writeFile (problemFile ++ ".dot") (pprDot sol)
#endif
        system (printf "dot -Tpdf %s -o %s.pdf " fp problemFile)
        -- hPutStrLn stderr (printf "Log written to %s.pdf" file)
        P.return ()

-- ------------------------------
-- Command Line Options handling
-- ------------------------------
usage = "Narradar - Automated Narrowing Termination Proofs"

getOptions = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute opts args
  case errors of
    [] -> do
      opts <- foldl (P.>>=) (P.return defOpts) actions
      let problemFile = fromMaybe "INPUT" (listToMaybe nonOptions)
      input <- maybe getContents readFile (listToMaybe nonOptions)
      P.return (opts{problemFile,input}, nonOptions, errors)
    _  -> putStrLn ("Error: " ++ unwords errors) >> putStrLn (usageInfo usage opts) >> exitWith (ExitFailure (-1))

-- data Options where Options :: (TRSC f, Ppr f) => FilePath -> PPT id f Html IO -> Bool -> Options

data Options =  Options { problemFile :: FilePath
                        , input       :: String
                        , diagrams    :: Bool
                        , verbose     :: Int
                        }

defOpts = Options{ problemFile = "", input = "", diagrams = True, verbose = 0}

--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option ""  ["nodiagrams"] (NoArg $ \opts  -> P.return opts{diagrams = False}) "Do not produce a pdf proof file"
#ifndef GHCI
       , Option "t" ["timeout"] (ReqArg setTimeout "SECONDS") "Timeout in seconds (default:none)"
#endif
       , Option "v" ["verbose"] (OptArg (\i opts -> maybe (P.return 1) readIO i P.>>= \i' -> P.return opts{verbose=i'}) "LEVEL") "Verbosity level (0-2)"
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) P.>> exitSuccess)) "Displays this help screen"
       ]

-- data NiceSolver where NiceSolver :: (TRSC f, Ppr f) => PPT id f Html IO -> (ProblemProofG id Html f -> String) -> NiceSolver

setTimeout arg opts = do
  scheduleAlarm (read arg)
  installHandler sigALRM  (Catch (putStrLn "timeout" P.>> exitImmediately (ExitFailure (-1)))) Nothing
  P.return opts
