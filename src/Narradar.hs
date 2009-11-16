{-# LANGUAGE CPP #-}
{-# LANGUAGE OverlappingInstances, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narradar ( narradarMain, prologMain
                , Options(..), defOpts
                , PprTPDBDot(..)      -- module Narradar.Framework.GraphViz
                , module Narradar.Processor.Graph
                , module Narradar.Processor.RPO
                , module Narradar.Processor.ReductionPair
                , module Narradar.Processor.GraphTransformation
                , module Narradar.Processor.UsableRules
                , module Narradar.Processor.InfinitaryProblem
                , module Narradar.Processor.NarrowingProblem
                , module Narradar.Processor.InitialGoalNarrowingProblem
                , module Narradar.Processor.ExtraVariables
                , module Narradar.Processor.PrologProblem
                , module Narradar.Processor.RelativeProblem
                , module Narradar.Processor.SubtermCriterion
                , module Narradar.Types
                ) where


import Control.Monad.Free
import Data.Foldable (Foldable)
import Data.Maybe
import Data.Monoid
import System.Cmd
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Posix.Process
import System.Posix.Signals
import System.Console.GetOpt
import Text.ParserCombinators.Parsec (parse, runParser)
import Text.Printf
import qualified Language.Prolog.Syntax as Prolog

import Prelude as P

import Narradar.Framework

import Narradar.Types hiding (note, dropNote)
import Narradar.Framework.GraphViz
import Narradar.Utils

import Narradar.Types.Problem.Relative
import Narradar.Types.Problem.InitialGoal
import Narradar.Processor.Graph
import Narradar.Processor.GraphTransformation
import Narradar.Processor.RPO
import Narradar.Processor.InfinitaryProblem
import Narradar.Processor.NarrowingProblem
import Narradar.Processor.InitialGoalNarrowingProblem
import Narradar.Processor.UsableRules
import Narradar.Processor.ReductionPair
import Narradar.Processor.ExtraVariables
import Narradar.Processor.PrologProblem
import Narradar.Processor.RelativeProblem
import Narradar.Processor.SubtermCriterion

narradarMain :: forall mp.
                 (IsMZero mp, Foldable mp
                 ,Dispatch (Problem Rewriting  (NTRS Id))
                 ,Dispatch (Problem IRewriting (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id)Rewriting) (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id)IRewriting) (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) (InitialGoal (TermF Id) Rewriting))  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) (InitialGoal (TermF Id) IRewriting))  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) Rewriting)  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) IRewriting)  (NTRS Id))
                 ,Dispatch (Problem Narrowing  (NTRS Id))
                 ,Dispatch (Problem CNarrowing (NTRS Id))
                 ,Dispatch (Problem (NarrowingGoal Id) (NTRS Id))
                 ,Dispatch (Problem (CNarrowingGoal Id) (NTRS Id))
                 ,Dispatch PrologProblem
                 ) => (forall a. mp a -> Maybe a) -> IO ()
narradarMain run = do
  (flags@Options{..}, _, _errors) <- getOptions
  tmp <- getTemporaryDirectory
  let printDiagram :: Proof (PrettyInfo, DotInfo) mp a -> IO ()
      printDiagram proof
       | isNothing pdfFile = return ()
       | isJust pdfFile    = withTempFile tmp "narradar.dot" $ \fp h -> do
                               let dotSrc  = dotProof' DotProof{showFailedPaths = verbose > 1} proof
                                   the_pdf = fromJust pdfFile
                               hPutStrLn h dotSrc
                               hClose h
#ifdef DEBUG
                               when (verbose > 1) $ writeFile (the_pdf ++ ".dot") dotSrc
#endif
                               ignore $ system (printf "dot -Tpdf %s -o %s" fp the_pdf)
                               hPutStrLn stderr ("PDF proof written to " ++ the_pdf)

  a_problem <- eitherM $ narradarParse problemFile input

  let proof    = dispatchAProblem a_problem
      sol      = run (runProof proof)
      diagrams = isJust pdfFile

  case sol of
    Just sol -> do putStrLn "YES"
                   when diagrams $ printDiagram sol
                   when (verbose>0) $ print $ pPrint sol

    Nothing  -> do
             putStrLn "MAYBE"
             when (diagrams && verbose > 0) $ do
                  print $ pPrint proof
                  printDiagram (sliceWorkDone proof)
  where

prologMain :: forall mp.
                 (IsMZero mp, Foldable mp
                 ,Dispatch PrologProblem
                 ) => (forall a. mp a -> Maybe a) -> IO ()
prologMain run = do
  (flags@Options{..}, _, _errors) <- getOptions
  tmp <- getTemporaryDirectory
  let printDiagram :: Proof (PrettyInfo, DotInfo) mp a -> IO ()
      printDiagram proof
       | isNothing pdfFile = return ()
       | isJust pdfFile    = withTempFile tmp "narradar.dot" $ \fp h -> do

                               let dotSrc  = dotProof' DotProof{showFailedPaths = verbose > 1} proof
                                   the_pdf = fromJust pdfFile
                               hPutStrLn h dotSrc
                               hClose h
#ifdef DEBUG
                               when (verbose > 1) $ writeFile (the_pdf ++ ".dot") dotSrc
#endif
                               ignore $ system (printf "dot -Tpdf %s -o %s" fp the_pdf)
                               hPutStrLn stderr ("PDF proof written to " ++ the_pdf)

  prologProblem <- eitherM $ parse prologParser problemFile input

  let proof    = dispatch prologProblem
      sol      = run (runProof proof)
      diagrams = isJust pdfFile

  case sol of
    Just sol -> do putStrLn "YES"
                   when diagrams $ printDiagram sol
                   when (verbose>0) $ print $ pPrint sol

    Nothing  -> do
             putStrLn "MAYBE"
             when (diagrams && verbose > 0) $ do
                  print $ pPrint proof
                  printDiagram (sliceWorkDone proof)
  where

-- ------------------------------
-- Command Line Options handling
-- ------------------------------
usage = "Narradar - Automated Narrowing Termination Proofs"

getOptions = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute opts args
  case errors of
    [] -> do
      let problemFile = fromMaybe "INPUT" (listToMaybe nonOptions)
      input <- maybe getContents readFile (listToMaybe nonOptions)
      opts <- foldl (P.>>=) (P.return defOpts{problemFile,input}) actions
      P.return (opts, nonOptions, errors)
    _  -> putStrLn ("Error: " ++ unwords errors) >> putStrLn (usageInfo usage opts) >> exitWith (ExitFailure (-1))

data Options =  Options { problemFile :: FilePath
                        , pdfFile     :: Maybe FilePath
                        , input       :: String
                        , verbose     :: Int
                        }

defOpts = Options{ problemFile = "", pdfFile = Nothing, input = "", verbose = 0}

--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option ""  ["pdf"] (OptArg setPdfPath "PATH") "Produce a pdf proof file (implied by -v)"
#ifndef GHCI
       , Option "t" ["timeout"] (ReqArg setTimeout "SECONDS") "Timeout in seconds (default:none)"
#endif
       , Option "v" ["verbose"] (OptArg setVerbosity "LEVEL") "Verbosity level (0-2)"
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) P.>> exitSuccess)) "Displays this help screen"
       ]

setTimeout arg opts = do
  scheduleAlarm (read arg)
  installHandler sigALRM  (Catch (putStrLn "timeout" P.>> exitImmediately (ExitFailure 2))) Nothing
  P.return opts

setVerbosity Nothing opts@Options{..} = P.return opts{verbose=1, pdfFile = pdfFile `mplus` Just (problemFile <.> "pdf")}

setVerbosity (Just i) opts@Options{..}
    = do {i <- readIO i; P.return opts{verbose=i, pdfFile = pdfFile `mplus` Just (problemFile <.> "pdf")}}
         `catch` (\e -> error "cannot parse the verbosity level")

setPdfPath Nothing  opts = P.return opts{ pdfFile = Just (problemFile opts <.> "pdf") }
setPdfPath (Just f) opts = P.return opts{ pdfFile = Just $ f }