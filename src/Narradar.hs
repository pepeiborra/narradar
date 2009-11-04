{-# LANGUAGE CPP #-}
{-# LANGUAGE OverlappingInstances, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narradar ( narradarMain, Options(..), defOpts
                , module Narradar.Framework
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
                , module Narradar.Types
                ) where


import Control.Monad.Free
import Data.Foldable (Foldable)
import Data.Maybe
import Data.Monoid
import System.Cmd
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

narradarMain :: forall mp.
                 (IsMZero mp, Foldable mp
--                 ,Dispatch (NProblem  (InitialGoal (TermF (Identifier String)) CNarrowing) (Identifier String))
--                 ,Dispatch (NProblem  (InitialGoal (TermF (Identifier String))  Narrowing) (Identifier String))
                 ,Dispatch (NProblem  (Relative  (NTRS (Identifier String)) Rewriting)  (Identifier String))
                 ,Dispatch (NProblem  Narrowing  (Identifier String))
                 ,Dispatch (NProblem  CNarrowing (Identifier String))
                 ,Dispatch (NProblem  (NarrowingGoal (Identifier String)) (Identifier String))
                 ,Dispatch (NProblem  (CNarrowingGoal (Identifier String)) (Identifier String))
                 ,Dispatch (NProblem  Rewriting  (Identifier String))
                 ,Dispatch (NProblem  IRewriting (Identifier String))
                 ,Dispatch PrologProblem
                 ) => (forall a. mp a -> Maybe a) -> IO ()
narradarMain run = do
  (flags@Options{..}, _, _errors) <- getOptions

  let printDiagram :: Proof (PrettyInfo, DotInfo) mp a -> IO ()
      printDiagram proof
       | isNothing pdfFile = return ()
       | isJust pdfFile    = withTempFile "." "narradar.dot" $ \fp h -> do

                               let dotSrc  = dotProof' DotProof{showFailedPaths = verbose > 1} proof
                                   the_pdf = fromJust pdfFile
                               hPutStrLn h dotSrc
                               hClose h
#ifdef DEBUG
                               when (verbose > 1) $ writeFile (the_pdf ++ ".dot") dotSrc
#endif
                               ignore $ system (printf "dot -Tpdf %s -o %s.pdf " fp the_pdf)
                               putStrLn ("PDF proof written to " ++ the_pdf ++ ".pdf")

  a_problem <- eitherM $ runParser narradarParser mempty "INPUT" input

  let proof    = dispatchAProblem a_problem
      sol      = run (runProof proof)
      diagrams = isJust pdfFile

  case sol of
    Just sol -> do putStrLn "YES"
                   when (verbose>0) $ do
                          print $ pPrint sol
                          when diagrams $ printDiagram sol

    Nothing  -> do
             putStrLn "MAYBE"
             when (diagrams && verbose > 0) $ do
                  print $ pPrint proof
                  printDiagram (sliceWorkDone proof)
  where
    dispatchAProblem (ARewritingProblem p)         = dispatch p
    dispatchAProblem (AIRewritingProblem p)        = dispatch p
    dispatchAProblem (ANarrowingProblem p)         = dispatch p
    dispatchAProblem (ACNarrowingProblem p)        = dispatch p
    dispatchAProblem (ARelativeRewritingProblem p) = dispatch p
    dispatchAProblem (AGoalNarrowingProblem p)     = dispatch p
    dispatchAProblem (AGoalCNarrowingProblem p)    = dispatch p
    dispatchAProblem (APrologProblem p)            = dispatch p


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

setVerbosity Nothing opts@Options{..} = P.return opts{verbose=1, pdfFile = pdfFile `mplus` Just (dropExtension problemFile)}

setVerbosity (Just i) opts@Options{..}
    = do {i <- readIO i; P.return opts{verbose=i, pdfFile = pdfFile `mplus` Just problemFile}}
         `catch` (\e -> error "cannot parse the verbosity level")

setPdfPath Nothing  opts = P.return opts{ pdfFile = Just $ dropExtension (problemFile opts) }
setPdfPath (Just f) opts = P.return opts{ pdfFile = Just $ dropExtension f }