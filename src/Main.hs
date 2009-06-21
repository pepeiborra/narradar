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

import ArgumentFiltering (bestHeu, typeHeu, typeHeu2, innermost)
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
  (Options problemFile (NiceSolver solver pprSol) diagrams, _, errors) <- getOptions
  sol <- runProofT solver
  putStrLn$ if isSuccess sol then "YES" else "NO"
  when diagrams $ withTempFile "." "narradar.dot" $ \fp h -> do
        hPutStrLn h (pprSol sol)
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
  return (Options problemFile (someSolver problemFile input) diagramsFlag, nonOptions, errors)

-- data Options where Options :: (TRSC f, Ppr f) => FilePath -> PPT id f Html IO -> Bool -> Options

data Options =  Options { problemFile :: FilePath
                        , solver      :: NiceSolver
                        , diagrams    :: Bool
                        }

data Flags id = Flags { solverFlag      :: Maybe String
                      , diagramsFlag    :: Bool
                      }

defFlags = Flags{ solverFlag       = Nothing
                , diagramsFlag     = True
                }
--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option "s" ["solver"]  (ReqArg (\arg opts -> returnM opts{solverFlag = Just arg}) "DESC")            "DESC = N | BN | PL [LOCAL path|WEB|SRV timeout] (default: automatic)"
       , Option ""  ["nodiagrams"] (NoArg $ \opts  -> returnM opts{diagramsFlag = False})                     "Do not produce a pdf proof file"
       , Option "t" ["timeout"] (ReqArg (\arg opts -> scheduleAlarm (read arg) >> return opts) "SECONDS")     "Timeout in seconds (default:none)"
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) >> exitSuccess))         "Displays this help screen"
       ]

type LSolver id f = ProblemG id f -> PPT LId BBasicLId Html IO
data SomeSolver where LabelSolver  :: ProblemType Id  -> LSolver Id  BBasicId  -> SomeSolver
                      SimpleSolver :: ProblemType LId -> LSolver LId BBasicLId -> SomeSolver
data SolverType id f where Labeller :: SolverType Id BBasicId
                           Simple   :: SolverType LId BBasicLId

data NiceSolver where NiceSolver :: (TRSC f, Ppr f) => PPT id f Html IO -> (ProblemProofG id Html f -> String) -> NiceSolver

getSolver :: SomeSolver -> SolverType id f -> Maybe (ProblemType id, LSolver id f)
getSolver (LabelSolver  typ s) Labeller = Just (typ, s)
getSolver (SimpleSolver typ s) Simple   = Just (typ, s)
getSolver _ _ = Nothing

parseTRS :: ProblemType Id -> FilePath -> String -> PPT Id BasicId Html IO
parseTRS typ file txt = wrap' $ do
                      rules :: [Rule Basic] <- eitherIO$ parseFile trsParser file txt
                      let trs = mkTRS rules :: NarradarTRS String Basic'
                      return (mkGoalProblem bestHeu AllTerms $ mkDPProblem Narrowing trs)

parseProlog :: String -> PPT String Basic' Html IO
parseProlog = wrap' . return . either error return . parsePrologProblem

parseSolver "N"  file txt = NiceSolver (parseTRS Narrowing  file txt >>= narradarSolver) pprDot
parseSolver "BN" file txt = NiceSolver (parseTRS BNarrowing file txt >>= narradarSolver) pprDot
parseSolver "PL" file txt = NiceSolver (parseProlog  txt >>= prologSolver) pprDot
parseSolver "PL_one" file txt = NiceSolver (parseProlog txt >>= prologSolver_one) pprDot
parseSolver "PL_inn" file txt = NiceSolver (parseProlog txt >>= prologSolver' (\_ _ -> innermost) (aproveSrvP 30)) pprDot
--parseSolver "PL_typ2" file txt = NiceSolver (parseProlog txt >>= prologSolver' ((typeHeu2.) . const) (aproveSrvP 30)) pprDot
{-
--parseSolver "PL_rhs" = LabelSolver Prolog      prologSolver_rhs

parseSolver "PL_noL" = LabelSolver Prolog      prologSolver_noL
parseSolver "PL_inn" = LabelSolver Prolog    $ prologSolver' (\_ _ -> innermost) (aproveSrvP 30)
parseSolver "PL_typ2"= LabelSolver Prolog    $ prologSolver' ((typeHeu2.) . const) (aproveSrvP 30)
parseSolver "PL_typ" = LabelSolver Prolog    $ prologSolver' ((typeHeu.)  . const) (aproveSrvP 30)
parseSolver ('P':'L':' ': (parseAprove -> Just k)) = LabelSolver Prolog (prologSolver' ((typeHeu.) . const) k)
--parseSolver ('P':'L':'_':'r':'h':'s':' ': (parseAprove -> Just k)) = LabelSolver Prolog (prologSolver_rhs' k)
parseSolver ('P':'L':'_':'o':'n':'e':' ': (parseAprove -> Just k)) = LabelSolver Prolog (prologSolver_one' ((typeHeu.) . const) k)
parseSolver _ = error "Could not parse the description. Expected (LOCAL path|WEB|SRV timeout)"
-}
parseAprove = go1 where
    go0 _                                 = Nothing
    go1 (prefixedBy "SRV"   -> Just timeout) | [(t,[])] <- reads timeout = Just (aproveSrvP t)
    go1 (prefixedBy "WEB"   -> Just [])   = Just aproveWebP
    go1 (prefixedBy "LOCAL "-> Just path) = Just $ aproveLocalP path
    go1 _                                 = Nothing

prefixedBy [] xx = Just xx
prefixedBy (p:pp) (x:xx) | p == x = prefixedBy pp xx
                         | otherwise = Nothing

eitherIO = either (error.show) return
