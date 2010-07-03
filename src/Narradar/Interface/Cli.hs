{-# LANGUAGE CPP #-}
{-# LANGUAGE OverlappingInstances, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards, PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Interface.Cli
        (narradarMain, prologMain
        , Options(..), defOpts
        ) where

import Control.Concurrent
import Control.Exception (evaluate)
import qualified Control.Exception as CE
import Control.Monad.Free
import Data.Foldable (Foldable)
import Data.Maybe
import Data.Monoid
import Data.Traversable (Traversable)
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
import Text.XHtml (toHtml)
import qualified Language.Prolog.Syntax as Prolog

import Prelude as P

import Narradar
import Narradar.Framework
import Narradar.Framework.GraphViz (dotProof', DotProof(..))
import Narradar.Utils
import MuTerm.Framework.DotRep (DotInfo)
import MuTerm.Framework.Output

#ifdef TESTING
import Properties (properties)
import Test.Framework.Runners.Console
import Test.Framework.Options
import Test.Framework.Runners.Options
#endif

narradarMain :: forall mp.
                 (IsMZero mp, Traversable mp
                 ,Dispatch (Problem Rewriting  (NTRS Id))
                 ,Dispatch (Problem IRewriting (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id) Rewriting)  (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id) IRewriting) (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id) Narrowing)  (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id) INarrowing) (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) (InitialGoal (TermF Id) Rewriting))  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) (InitialGoal (TermF Id) IRewriting))  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) Rewriting)  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) IRewriting)  (NTRS Id))
                 ,Dispatch (Problem Narrowing  (NTRS Id))
                 ,Dispatch (Problem CNarrowing (NTRS Id))
                 ,Dispatch PrologProblem
                 ) => (forall a. mp a -> Maybe a) -> IO ()
narradarMain run = catchTimeout $ do
  (flags@Options{..}, _, _errors) <- getOptions
  let echoV str = when (verbose>1) $ hPutStrLn stderr str
  tmp <- getTemporaryDirectory
  let printDiagram :: Proof (PrettyInfo, DotInfo) mp a -> IO ()
      printDiagram proof
       | isNothing pdfFile = return ()
       | Just the_pdf <- pdfFile = withTempFile tmp "narradar.dot" $ \fp h -> do
                               let dotSrc  = dotProof' DotProof{showFailedPaths = verbose > 1} proof
                               hPutStrLn h dotSrc
                               hClose h
#ifdef DEBUG
                               when (verbose > 1) $ writeFile (the_pdf ++ ".dot") dotSrc
#endif
                               let dotCmd = printf "dot -Tpdf %s -o%s" fp the_pdf
                               echoV dotCmd
                               dotOk <- system dotCmd
                               echo ("PDF proof written to " ++ the_pdf)
                               return (dotOk == ExitSuccess, ())

  a_problem <- eitherM $ narradarParse problemFile input

  let proof    = dispatchAProblem a_problem
  sol <- maybe (fmap Just) withTimeout timeout $
         evaluate $ run (runProof proof)
  let diagrams = isJust pdfFile

  case join sol of
    Just sol -> do putStrLn "YES"
                   when diagrams $ printDiagram sol
                   when (verbose>0) $ print $ pPrint sol

    Nothing  -> do
             putStrLn "MAYBE"
             let proof' = sliceProof proof
             when (verbose > 1) $ print $ pprProofFailures proof'
--             when (verbose > 1 && diagrams) $ printDiagram proof'
  where
    catchTimeout = (`CE.catch` \TimeoutException -> putStrLn "MAYBE" >> exitSuccess)


withTimeout t m = do
  res  <- newEmptyMVar
  done <- newMVar ()

  worker_id <- forkIO $ (`CE.catch` \TimeoutException -> return ()) $ do
             val <- m
             takeMVar done
             putMVar res (Just val)

  clocker_id <- forkIO $ do
             threadDelay (t * 1000000)
             takeMVar done
             throwTo worker_id TimeoutException
             putMVar res Nothing

  takeMVar res

prologMain :: forall mp.
                 (IsMZero mp, Traversable mp
                 ,Dispatch PrologProblem
                 ) => (forall a. mp a -> Maybe a) -> IO ()
prologMain run = catchTimeout $ do
  (flags@Options{..}, _, _errors) <- getOptions
  let echoV str = when (verbose>1) $ hPutStrLn stderr str
  tmp <- getTemporaryDirectory
  let printDiagram :: Proof (PrettyInfo, DotInfo) mp a -> IO ()
      printDiagram proof
       | isNothing pdfFile = return ()
       | Just the_pdf <- pdfFile = withTempFile tmp "narradar.dot" $ \fp h -> do
                               let dotSrc  = dotProof' DotProof{showFailedPaths = verbose > 1} proof
                               hPutStrLn h dotSrc
                               hClose h
#ifdef DEBUG
                               when (verbose > 1) $ writeFile (the_pdf ++ ".dot") dotSrc
#endif
                               let dotcmd = printf "dot -Tpdf %s -o%s" fp the_pdf
                               echoV dotcmd
                               dotok <- system dotcmd
                               echo ("PDF proof written to " ++ the_pdf)
                               return (dotok == ExitSuccess, ())

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
             when (verbose > 1) $ print $ pprProofFailures proof
             when (diagrams && verbose > 0) $ printDiagram (sliceProof proof)
  where
    catchTimeout = (`CE.catch` \TimeoutException -> putStrLn "MAYBE")
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
                        , timeout     :: Maybe Int
                        }

defOpts = Options{ problemFile = "", pdfFile = Nothing, input = "", verbose = 0, timeout = Nothing}

--opts :: [OptDescr (Flags f id -> Flags f id)]
opts = [ Option ""  ["pdf"] (OptArg setPdfPath "PATH") "Produce a pdf proof file (implied by -v2)"
#ifndef GHCI
       , Option "t" ["timeout"] (ReqArg setTimeout "SECONDS") "Timeout in seconds (default:none)"
#endif
       , Option "v" ["verbose"] (OptArg setVerbosity "LEVEL") "Verbosity level (0-2)"
       , Option "h?" ["help"]   (NoArg  (\   _     -> putStrLn(usageInfo usage opts) P.>> exitSuccess)) "Displays this help screen"
#ifdef TESTING
       , Option "" ["verify"] (OptArg runTests "THREADS")
                    "Run quickcheck properties and unit tests (# THREADS)"
#endif
       ]

#ifdef TESTING
runTests mb_threads _ = do
  defaultMainWithOpts properties runnerOpts
  exitSuccess
 where
  runnerOpts = RunnerOptions (fmap read mb_threads) (Just to) Nothing
  to = TestOptions {topt_seed = Nothing
                   ,topt_maximum_generated_tests = Just 5000
                   ,topt_maximum_unsuitable_generated_tests = Just 1000
                   ,topt_timeout = Just(Just (ms 3000)) }
  ms = (*1000000)
#endif

setTimeout arg opts = do
  let t = read arg
{-
  scheduleAlarm t
  t_id <- myThreadId
  installHandler sigALRM (Catch $ do
                            throwTo t_id TimeoutException
                            debug "timeout"
                          )
                         Nothing
-}
  P.return opts{timeout= Just t}

setVerbosity Nothing opts@Options{..} = P.return opts{verbose=1}

setVerbosity (Just "2") opts@Options{..}
    = do {P.return opts{verbose=2, pdfFile = pdfFile `mplus` Just (problemFile <.> "pdf")}}
         `catch` (\e -> error "cannot parse the verbosity level")

setVerbosity (Just i) opts@Options{..}
    = do {i <- readIO i; P.return opts{verbose=i}}
         `catch` (\e -> error "cannot parse the verbosity level")

setPdfPath Nothing  opts = P.return opts{ pdfFile = Just (problemFile opts <.> "pdf") }
setPdfPath (Just f) opts = P.return opts{ pdfFile = Just f }