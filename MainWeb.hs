
import Network.CGI
import TRS.FetchRules
import TRS.FetchRules.TRS
import Text.XHtml

import Problem
import Types hiding ((!))
import Solver

main = runCGI (handleErrors cgiMain)

cgiMain = do
  mb_rules  <- getInput "TRS"
  case mb_rules of
    Nothing -> outputError 100 "missing parameter" []
    Just rules -> do
     let ei_trs = parseFile trsParser "input" rules
     case ei_trs of
       Left parse_error -> output $ show parse_error
       Right trs -> do
          res <- liftIO $ solveNarrowing $ mkTRS trs
          output$ renderHtml $
           if success res
             then thediv ! [identifier "title"] << h3 << "Termination was proved succesfully" +++ res
             else thediv ! [identifier "title"] << h3 << "Termination could not be proved"    +++ res