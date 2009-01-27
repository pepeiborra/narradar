{-# LANGUAGE PackageImports, NoImplicitPrelude #-}

{-
  This module needs to be reconverted to use GetOpt.
  Right now there are two many options and because the
  ad-hoc approach used is not composable, it is hard to
  add support for Basic Narrowing and/or for Prolog.
-}
module Main where

import "monad-param" Control.Monad.Parameterized
import System.Cmd
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import Text.Printf
import Text.XHtml
import qualified Text.ParserCombinators.Parsec as Parsec

import Prelude hiding (Monad(..))

import Prolog
import TRS.FetchRules
import TRS.FetchRules.TRS
import Types hiding ((!))
import Utils
import Solver
import Proof
import GraphViz
import GraphTransformation
import NarrowingProblem
import Output
import qualified Language.Prolog.Parser as Prolog

logfile = "narradar.log"

main :: IO ()
main = do
  args <- getArgs
  case args of
--    [file, "SKEL"]      -> parseIt file (print.pprSkelt. (startSolver >=> pureSolver))
--    [file, "DOT"]       -> parseIt file (putStrLn.pprDot.(startSolver >=> pureSolver))
    [file, "SRV"]       -> work Nothing file srvSolver
    [file, "SERIAL"]    -> work Nothing file srvSolverSerial
    [file, "WEB"]       -> work Nothing file webSolver
    [file, aprove_path] -> work Nothing file (localSolver' aprove_path)
    [file, "GOAL", goal]-> work (either (error.show) Just $ parseGoal goal) file srvSolver
    [file, "PROLOG", goal]-> workProlog (either (error.show) id $ parseGoal goal) file srvSolver
    [file]              -> work Nothing file srvSolver
    _ -> do n <- getProgName
            putStrLn$ "Narradar - Automated Narrowing Termination Proofs\n USAGE: " ++ n ++
                        " <system.trs> [path_to_aprove|SRV|WEB|DOT|SKEL|SERIAL]"
  where parseIt file k = do
              contents <- readFile file
              case parseFile trsParser file contents of
                Left error -> print error >> exitWith (ExitFailure 1)
                Right trs_ -> k (mkTRS trs_)
        work goal file slv = parseIt file $ \trs -> do
                  sol <- runSolver slv (mkBNDPProblem goal trs)
                  putStr (renderHtml (page sol))
                  withTempFile "." "narradar.dot" $ \fp h -> do
                                hPutStrLn h (pprDot sol)
                                putStrLn (pprDot sol)
                                system (printf "dot -Tpdf %s -o %s.pdf" fp logfile)
                                hPutStrLn stderr (printf "Log written to %s.pdf" logfile)
        workProlog goal file slv = do
                  ei_pgm <- Parsec.parseFromFile Prolog.program file
                  case ei_pgm of
                    Left parseError -> error (show parseError)
                    Right pgm -> do
                                sol <- runSolver slv (mkPrologProblem goal pgm)
                                putStr (renderHtml (page sol))
                                withTempFile "." "narradar.dot" $ \fp h -> do
                                 hPutStrLn h (pprDot sol)
                                 putStrLn (pprDot sol)
                                 system (printf "dot -Tpdf %s -o %s.pdf" fp logfile)
                                 hPutStrLn stderr (printf "Log written to %s.pdf" logfile)


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
  divres = thediv ! [identifier "title"] << h3 << title +++ res


cssSheet src = thelink ! [rel "stylesheet", thetype "text/css", href src] << noHtml
jsScript thesrc = script ! [thetype "text/javascript", src thesrc] << noHtml
