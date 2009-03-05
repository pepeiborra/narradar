{-# LANGUAGE PatternGuards, ViewPatterns, ScopedTypeVariables #-}
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

import Prelude

import Narradar hiding ((!), return, Bind(..))
import Narradar.Output hiding (Ppr)
import Narradar.Solver
import Narradar.Proof
import Narradar.Utils (withTempFile)
import Narradar.GraphViz
import Control.Monad.Free

main = runCGI (handleErrors cgiMain)

cgiMain = do
  mb_input  <- getInput "TRS"
  mb_visual <- getInput "LOG"
  mb_type   <- getInput "TYPE"
  mb_goal   <- getInput "GOAL" >>= \mb_g -> return(mb_g >>= \g -> let g' = filter (/= ' ') g in if null g' then Nothing else return g')
  mb_strat  <- getInput "STRAT"
  case (mb_input, mb_type) of
    (Just input, Just typ) -> do
       (success, dot_proof, html_proof) <- liftIO $  case typ of
                       "PROLOG" -> let input' = maybe input ((input ++) .( "\n%query: " ++)) mb_goal
                                   in  process(parseProlog input' >>= stratSolver mb_strat)
                       "BASIC"  -> process(parseTRS BNarrowing input >>= narradarSolver)
                       "FULL"   -> process(parseTRS  Narrowing input >>= narradarSolver)
       proof_log <- liftIO$ withTempFile "/tmp" "narradar-log-" $ \fp h -> do
                      let fn = takeBaseName fp ++ ".pdf"
                      hPutStrLn h dot_proof
                      hClose h
                      system (printf "dot -Tpdf %s -o /home/narradar/public_html/logs/%s" fp fn)
                      return ("See a visual log of the proof " +++
                                anchor ! [href ("logs/" ++ fn)] << "here")
       output$ renderHtml $
                 if success
                    then thediv ! [identifier "title"] << h3 << "Termination was proved succesfully." +++ p << proof_log +++ p << html_proof
                    else thediv ! [identifier "title"] << h3 << "Termination could not be proved."    +++ p << proof_log +++ p << html_proof
    _ -> outputError 100 "missing parameter" []

process :: (Ppr f, Show id) =>  PPT id f Html IO -> IO (Bool, String, Html)
process p = go(runProofT p >>= \sol -> return (isSuccess sol, pprDot sol, toHtml sol))

stratSolver Nothing           = prologSolver
stratSolver (Just "TYPEHEU")  = prologSolver -- "Type Heuristic (unbounded positions)"
stratSolver (Just "TYPEHEU2") = prologSolver' (\typ _ -> typeHeu2 typ) (aproveSrvP defaultTimeout)
stratSolver (Just "INN")      = prologSolver' (\_   _ -> innermost)    (aproveSrvP defaultTimeout)