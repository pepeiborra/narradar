{-# LANGUAGE CPP #-}
{-# LANGUAGE PackageImports, NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module Main where

import Control.Applicative
-- import "monad-param" Control.Monad.Parameterized
import Control.Monad
import Data.List
import Data.Maybe
import Data.Monoid
import System.Cmd
import System.Environment
import System.Exit
import System.IO
import System.Posix.Process
import System.Posix.Signals
import System.Console.GetOpt
import Text.Printf
import Text.Regex.Posix
import Text.XHtml as Html


import Prelude -- hiding (Monad(..))
import qualified Prelude as P

import ArgumentFiltering (bestHeu, typeHeu, innermost)
import PrologProblem
import TRS.FetchRules
import TRS.FetchRules.TRS
import Types hiding ((!))
import DPairs
import Utils
import qualified Solver
import Solver
import Proof hiding (problem)
import GraphViz
import NarrowingProblem
import Control.Monad.Free
import Aprove

returnM = return

main :: IO ()
main = do
#ifndef GHCI
  installHandler sigALRM  (Catch (putStrLn "timeout" >> exitImmediately (ExitFailure (-1)))) Nothing
#endif
  (Options{..}, _, errors) <- getOptions
  sol <- runSolver solver (htmlProof problem)
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
  flags0@Flags{..} <- foldl (>>=) (return defFlags) actions
  let solverFlag' = if (".pl" `isSuffixOf` problemFile) && isNothing solverFlag then "PL" else fromMaybe "N" solverFlag
      problemFile = fromMaybe "INPUT" (listToMaybe nonOptions)
      someSolver  = parseSolver solverFlag'
  input <- maybe getContents readFile (listToMaybe nonOptions)
  opts <- case (getSolver someSolver Labeller, getSolver someSolver Simple, parsePrologProblem input goalFlags, parseFile trsParser problemFile input) of
             (Just (Prolog, s),_, Right p,_) -> return (Options Prolog problemFile (return p) s diagramsFlag)
             (_,Just (typ, s), _, Right (trs :: [Rule Basic])) ->
                 let p = mkGoalProblem bestHeu (maybe AllTerms (`FromGoal` Nothing) $ listToMaybe
                                                     (map (either (error.show) id . parseGoal) goalFlags))
                                       (mkDPProblem typ (mkTRS trs))
                 in return (Options typ problemFile p s diagramsFlag)
             (Just (Prolog, _), _, Left parseError, _) -> putStrLn parseError >> exitWith (ExitFailure 1)
             (_, _, _, Left parseError)                -> print parseError    >> exitWith (ExitFailure 1)
  return (opts, nonOptions, errors)

data Options = forall id f . Options { problemType :: ProblemType id
                                     , problemFile :: FilePath
                                     , problem     :: ProblemProofG id Html f
                                     , solver      :: LSolver id f
                                     , diagrams    :: Bool
                                     }

data Flags id = Flags { solverFlag      :: Maybe String
                      , goalFlags       :: [String]
                      , diagramsFlag    :: Bool
                      }

defFlags = Flags{ solverFlag       = Nothing
                , goalFlags        = []
                , diagramsFlag     = True
                }
--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option "s" ["solver"]  (ReqArg (\arg opts -> returnM opts{solverFlag = Just arg}) "DESC")            "DESC = N | BN | PL [LOCAL path|WEB|SRV timeout] (default: automatic)"
       , Option "g" ["goal"]    (ReqArg (\arg opts -> returnM opts{goalFlags  = arg : goalFlags opts}) "GOAL") "Goal to be solved, if any. Multiple goals can be introduced in separate uses of this flag"
       , Option ""  ["nodiagrams"] (NoArg $ \opts  -> returnM opts{diagramsFlag = False})                     "Do not produce a pdf proof file"
       , Option "t" ["timeout"] (ReqArg (\arg opts -> scheduleAlarm (read arg) >> return opts) "SRCONDS")     "Timeout in seconds (default:none)"
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) >> exitSuccess))         "Displays this help screen"
       ]

type LSolver id f = ProblemG id f -> PPT LId BBasicLId Html IO
data SomeSolver where LabelSolver  :: ProblemType Id  -> LSolver Id  BBasicId  -> SomeSolver
                      SimpleSolver :: ProblemType LId -> LSolver LId BBasicLId -> SomeSolver
data SolverType id f where Labeller :: SolverType Id BBasicId
                           Simple   :: SolverType LId BBasicLId

getSolver :: SomeSolver -> SolverType id f -> Maybe (ProblemType id, LSolver id f)
getSolver (LabelSolver  typ s) Labeller = Just (typ, s)
getSolver (SimpleSolver typ s) Simple   = Just (typ, s)
getSolver _ _ = Nothing

parseSolver "N"      = SimpleSolver Narrowing  narradarSolver
parseSolver "BN"     = SimpleSolver BNarrowing narradarSolver
parseSolver "PL"     = LabelSolver Prolog      prologSolver
parseSolver "PL_rhs" = LabelSolver Prolog      prologSolver_rhs
parseSolver "PL_one" = LabelSolver Prolog      prologSolver_one
parseSolver "PL_noL" = LabelSolver Prolog      prologSolver_noL
parseSolver "PL_inn" = LabelSolver Prolog    $ prologSolver' (\_ _ -> innermost) (aproveSrvP 30)
parseSolver "PL_typ" = LabelSolver Prolog    $ prologSolver' ((typeHeu.) . const) (aproveSrvP 30)
parseSolver ('P':'L':' ': (parseAprove -> Just k)) = LabelSolver Prolog (prologSolver' ((typeHeu.) . const) k)
parseSolver ('P':'L':'_':'r':'h':'s':' ': (parseAprove -> Just k)) = LabelSolver Prolog (prologSolver_rhs' k)
parseSolver ('P':'L':'_':'o':'n':'e':' ': (parseAprove -> Just k)) = LabelSolver Prolog (prologSolver_one' ((typeHeu.) . const) k)
parseSolver _ = error "Could not parse the description. Expected (LOCAL path|WEB|SRV timeout)"

parseAprove = go1 where
    go0 _                                 = Nothing
    go1 (prefixedBy "SRV"   -> Just timeout) | [(t,[])] <- reads timeout = Just (aproveSrvP t)
    go1 (prefixedBy "WEB"   -> Just [])   = Just aproveWebP
    go1 (prefixedBy "LOCAL "-> Just path) = Just $ aproveLocalP path
    go1 _                                 = Nothing

prefixedBy [] xx = Just xx
prefixedBy (p:pp) (x:xx) | p == x = prefixedBy pp xx
                         | otherwise = Nothing