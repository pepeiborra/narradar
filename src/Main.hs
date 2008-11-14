module Main where

import System.Environment
import System.Exit
import System.IO
import Text.Printf
import Text.XHtml

import TRS.FetchRules
import TRS.FetchRules.TRS
import Types hiding ((!))
import Solver
import Problem


main = do
  args <- getArgs
  case args of
    [file, "SRV"]       -> work file solveNarrowingSrv
    [file, "WEB"]       -> work file solveNarrowingWeb
    [file, aprove_path] -> work file (solveNarrowingLocal' aprove_path)
    [file] -> work file (solveNarrowingLocal' "./runme")
    _ -> getProgName >>= \n -> printf "Narradar - Automated Narrowing Termination Proofs\n USAGE: %s <system.trs> [path_to_aprove] \n" n
  where work file aprove_slv = do
              contents <- readFile file
              case parseFile trsParser file contents of
                Left error -> print error >> exitWith (ExitFailure 1)
                Right trs_ -> do
                  sol <- aprove_slv (mkTRS trs_)
                  putStr (renderHtml (page sol))

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
