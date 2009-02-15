{-# LANGUAGE PackageImports, NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

{-
  This module needs to be reconverted to use GetOpt.
  Right now there are two many options and because the
  ad-hoc approach used is not composable, it is hard to
  add support for Basic Narrowing and/or for Prolog.
-}
module Main where

import "monad-param" Control.Monad.Parameterized
import Data.List
import System.Cmd
import System.Environment
import System.Exit
import System.IO
import Text.Printf
import Text.XHtml as Html


import Prelude hiding (Monad(..))
import qualified Prelude as P

import PrologProblem
import TRS.FetchRules
import TRS.FetchRules.TRS
import Types hiding ((!))
import Utils
import qualified Solver
import Solver -- hiding (prologSolver)
import Proof
import GraphViz
import NarrowingProblem
import Control.Monad.Free
import Aprove

-- prologSolver = allSolver' (wrap' . aproveWebProc)

main :: IO ()
main = do
  args <- getArgs
  case args of
--    [file, "SKEL"]      -> parseIt file (print.pprSkelt. (startSolver >=> pureSolver))
--    [file, "DOT"]       -> parseIt file (putStrLn.pprDot.(startSolver >=> pureSolver))
    [file, "SRV"]       -> readFile file >>= work Nothing file narradarSolver
    [file, "WEB"]       -> readFile file >>= work Nothing file webSolver
    [file, "GOAL", goal]-> readFile file >>= work (either (error.show) Just $ parseGoal goal) file narradarSolver
    ["PROLOG"]          -> getContents   P.>>= workProlog [] "narradar" prologSolver
    (file : "PROLOG" :g)-> readFile file P.>>= workProlog g file prologSolver
    (file : g) | ".pl" `isSuffixOf` file -> readFile file >>= workProlog g file prologSolver
--    [file, aprove_path] -> readFile file >>= work Nothing file (localSolver' aprove_path)
    [file]              -> readFile file >>= work Nothing file narradarSolver
    _ -> do n <- getProgName
            putStrLn$ "Narradar - Automated Narrowing Termination Proofs\n USAGE: " ++ n ++
                        " <system.trs> [path_to_aprove|SRV|WEB|DOT|SKEL|SERIAL]"
  where parseIt contents k = do
              case parseFile trsParser "" contents of
                Left error -> print error >> exitWith (ExitFailure 1)
                Right (trs_ :: [Rule Basic]) -> k (mkTRS trs_ :: NarradarTRS Id BBasicId)

--        work :: Maybe Goal -> String -> Solver Identifier Html IO BBasicId -> String -> IO ()
        work (goal::Maybe Goal) file slv txt = parseIt txt $ \trs -> do
                  sol :: ProblemProofG Id Html BBasicId <- runSolver slv (mkNDPProblem (maybe AllTerms FromGoal goal) trs)
                  putStr (renderHtml (page sol))
                  withTempFile "." "narradar.dot" $ \fp h -> do
                                hPutStrLn h (pprDot sol)
                                hFlush h
                                putStrLn (pprDot sol)
                                system (printf "dot -Tpdf %s -o %s.pdf" fp file)
                                hPutStrLn stderr (printf "Log written to %s.pdf" file)
        workProlog gg file slv txt = do
                  case parsePrologProblem txt gg of
                    Left parseError -> putStrLn parseError >> exitWith (ExitFailure 1)
                    Right (p :: ProblemG Identifier BBasicId) -> do
                                sol :: ProblemProofG LId Html BBasicLId <- runSolver slv (htmlProof $ P.return p)
                                putStrLn$ if isSuccess sol then "YES" else "NO"
                                withTempFile "." "narradar.dot" $ \fp h -> do
                                 hPutStrLn h (pprDot sol)
                                 hFlush h
                                 system (printf "dot -Tpdf %s -o %s.pdf " fp file)
                                 -- hPutStrLn stderr (printf "Log written to %s.pdf" file)
                                 return ()


page res = myhead +++ body << divres where
  myhead = header << ( thetitle << title
                   +++ cssSheet "style/narradar.css"
                   +++ cssSheet "style/thickbox.css"
                   +++ map jsScript [ "scripts/narradar.js"
                                    , "scripts/jquery.pack.js"
                                    , "scripts/jquery.form.js"
                                    , "scripts/jquery.blockUI.js"
                                    , "scripts/thickbox.js"
                                    ])
  title  = if isSuccess res
             then "Termination was proved succesfully"
             else "Termination could not be proven"
  divres = thediv ! [Html.identifier "title"] << h3 << title +++ res


cssSheet src = thelink ! [rel "stylesheet", thetype "text/css", href src] << noHtml
jsScript thesrc = script ! [thetype "text/javascript", src thesrc] << noHtml
