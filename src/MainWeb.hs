{-# LANGUAGE PatternGuards #-}
import Control.Applicative
import Control.Exception (bracket)
import Data.Maybe (isJust, maybeToList)
import Network.CGI
import TRS.FetchRules
import TRS.FetchRules.TRS
import Text.Printf
import Text.XHtml
import Text.ParserCombinators.Parsec (parse)

import System.Cmd
import System.FilePath
import System.IO

import PrologProblem
import NarrowingProblem
import Output
import Proof
import GraphViz
import Types hiding ((!))
import Utils
import Solver

main = runCGI (handleErrors cgiMain)

cgiMain = do
  mb_rules  <- getInput "TRS"
  mb_visual <- getInput "LOG"
  mb_type   <- getInput "TYPE"
  mb_goal   <- getInput "GOAL" >>= \mb_g -> return(mb_g >>= \g -> let g' = filter (/= ' ') g in if null g' then Nothing else return g')
  case (mb_rules, mb_type) of
    (Just rules, Just typ) -> do
                mkProblem typ rules mb_goal (processProblem (isJust mb_visual))
    _ -> outputError 100 "missing parameter" []

processProblem False problem = do
  res <- liftIO $ runSolver srvSolverSerial problem
  output$ renderHtml $
                 if isSuccess res
                    then thediv ! [identifier "title"] << h3 << "Termination was proved succesfully." +++ p << res
                    else thediv ! [identifier "title"] << h3 << "Termination could not be proved."    +++ p << res

processProblem True problem = do
  res <- liftIO $ runSolver srvSolver problem
  proof_log <- do liftIO$ withTempFile "/tmp" "narradar-log-" $ \fp h -> do
                                let fn = takeBaseName fp ++ ".pdf"
                                hPutStrLn h (pprDot res)
                                hClose h
                                system (printf "dot -Tpdf %s -o /home/narradar/public_html/logs/%s" fp fn)
                                return ("See a visual log of the proof " +++
                                          anchor ! [href ("logs/" ++ fn)] << "here")
  output$ renderHtml $
                 if isSuccess res
                    then thediv ! [identifier "title"] << h3 << "Termination was proved succesfully." +++ p << proof_log +++ p << res
                    else thediv ! [identifier "title"] << h3 << "Termination could not be proved."    +++ p << proof_log +++ p <<res

mkProblem "PROLOG" pgm mb_goal k  = either output k $ parsePrologProblem pgm (maybeToList mb_goal)
mkProblem "PROLOG2" pgm mb_goal k = either output k $ parsePrologProblem pgm (maybeToList mb_goal)
mkProblem typ rules mb_goal k = do
     let ei_trs = parseFile trsParser "input" rules
     case ei_trs of
       Left parse_error -> output $ show parse_error
       Right trs -> do
          let  mb_ei_goal =  parseGoal <$> mb_goal
          case mb_ei_goal of
            Just (Left parse_error) -> output ("Syntax error in the goal: " ++ show parse_error)
            _ | mb_goal' <- fromRight <$> mb_ei_goal -> do
                      case typ of
                       "FULL"   -> k $ mkNDPProblem  mb_goal' $ mkTRS trs
                       "BASIC"  -> k $ mkBNDPProblem mb_goal' $ mkTRS trs


fromRight (Right x) = x