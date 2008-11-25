import Control.Exception (bracket)
import Data.Maybe (isJust)
import Network.CGI
import TRS.FetchRules
import TRS.FetchRules.TRS
import Text.Printf
import Text.XHtml

import System.Cmd
import System.FilePath
import System.IO

import Problem
import Types hiding ((!))
import Utils
import Solver

main = runCGI (handleErrors cgiMain)

cgiMain = do
  mb_rules  <- getInput "TRS"
  mb_visual <- getInput "LOG"
  case mb_rules of
    Nothing -> outputError 100 "missing parameter" []
    Just rules -> do
     let ei_trs = parseFile trsParser "input" rules
     case ei_trs of
       Left parse_error -> output $ show parse_error
       Right trs -> do
          res <- liftIO $ runSolver srvSolver $ mkTRS trs
          proof_log <- if isJust mb_visual then do
                                liftIO$ withTempFile "/tmp" "narradar-log-" $ \fp h -> do
                                let fn = takeBaseName fp ++ ".pdf"
                                hPutStrLn h (pprDot res)
                                hClose h
                                system (printf "dot -Tpdf %s -o /home/narradar/public_html/logs/%s" fp fn)
                                return ("See a visual log of the proof " +++
                                          anchor ! [href ("logs/" ++ fn)] << "here")
                          else return noHtml

          output$ renderHtml $
           if isSuccess res
             then thediv ! [identifier "title"] << h3 << "Termination was proved succesfully." +++ proof_log +++ res
             else thediv ! [identifier "title"] << h3 << "Termination could not be proved."    +++ proof_log +++ res
