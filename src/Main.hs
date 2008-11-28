{-# LANGUAGE PackageImports, NoImplicitPrelude #-}
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


import Prelude hiding (Monad(..))

import TRS.FetchRules
import TRS.FetchRules.TRS
import Types hiding ((!))
import Utils
import Solver
import Problem
import GraphTransformation
import NarrowingProblem

logfile = "narradar.log"

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file, "SKEL"]      -> parseIt file (print.pprSkelt. (startSolver >=> mainSolverPure))
    [file, "DOT"]       -> parseIt file (putStrLn.pprDot.(startSolver >=> mainSolverPure))
    [file, "SRV"]       -> work file srvSolver
    [file, "SERIAL"]       -> work file srvSolverSerial
    [file, "WEB"]       -> work file webSolver
    [file, aprove_path] -> work file (localSolver' aprove_path)
    [file] -> work file srvSolver
    _ -> do n <- getProgName
            putStrLn$ "Narradar - Automated Narrowing Termination Proofs\n USAGE: " ++ n ++
                        " <system.trs> [path_to_aprove|SRV|WEB|DOT|SKEL]"
  where parseIt file k = do
              contents <- readFile file
              case parseFile trsParser file contents of
                Left error -> print error >> exitWith (ExitFailure 1)
                Right trs_ -> k (mkTRS trs_)
        work file slv = parseIt file $ \problem -> do
                  sol <- runSolver slv problem
                  putStr (renderHtml (page sol))
                  withTempFile "." "narradar.dot" $ \fp h -> do
                                hPutStrLn h (pprDot sol)
                                -- hClose h
                                system (printf "dot -Tpdf %s -o %s.pdf" fp logfile)
                                removeFile fp
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
