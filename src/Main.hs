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

import PrologProblem
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


main :: IO ()
main = do
  args <- getArgs
  case args of
--    [file, "SKEL"]      -> parseIt file (print.pprSkelt. (startSolver >=> pureSolver))
--    [file, "DOT"]       -> parseIt file (putStrLn.pprDot.(startSolver >=> pureSolver))
    [file, "SRV"]       -> readFile file >>= work Nothing file srvSolver
    [file, "WEB"]       -> readFile file >>= work Nothing file webSolver
    [file, "GOAL", goal]-> readFile file >>= work (either (error.show) Just $ parseGoal goal) file srvSolver
    ["PROLOG"]          -> getContents   >>= workProlog [] "narradar" srvSolver
    (file : "PROLOG" :g)-> readFile file >>= workProlog g file srvSolver
    [file]              -> readFile file >>= work Nothing file srvSolver
    [file, aprove_path] -> readFile file >>= work Nothing file (localSolver' aprove_path)
    _ -> do n <- getProgName
            putStrLn$ "Narradar - Automated Narrowing Termination Proofs\n USAGE: " ++ n ++
                        " <system.trs> [path_to_aprove|SRV|WEB|DOT|SKEL|SERIAL]"
  where parseIt contents k = do
              case parseFile trsParser "" contents of
                Left error -> print error >> exitWith (ExitFailure 1)
                Right trs_ -> k (mkTRS trs_)

        work goal file slv txt = parseIt txt $ \trs -> do
                  sol <- runSolver slv (mkNDPProblem goal trs)
                  putStr (renderHtml (page sol))
                  withTempFile "." "narradar.dot" $ \fp h -> do
                                hPutStrLn h (pprDot sol)
                                putStrLn (pprDot sol)
                                system (printf "dot -Tpdf %s -o %s.pdf" fp file)
                                hPutStrLn stderr (printf "Log written to %s.pdf" file)
        workProlog gg file slv txt = do
                  case parsePrologProblem txt gg of
                    Left parseError -> error parseError
                    Right p -> do
                                sol <- runSolver slv p
                                putStrLn$ if isSuccess sol then "YES" else "NO"
                                withTempFile "." "narradar.dot" $ \fp h -> do
                                 hPutStrLn h (pprDot sol)
                                 system (printf "dot -Tpdf %s -o %s.pdf 2> /dev/null > /dev/null" fp file)
                                 return ()
                                 -- hPutStrLn stderr (printf "Log written to %s.pdf" file)


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
