{-# LANGUAGE PackageImports, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
import Control.Applicative
import Control.Exception (bracket)
import qualified "monad-param" Control.Monad.Parameterized as P
import Data.Maybe
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

import Narradar hiding ((!))
import Narradar.Solver
import Narradar.Output
import Narradar.Proof
import Narradar.Utils (withTempFile)
import Narradar.GraphViz

main = runCGI (handleErrors cgiMain)

cgiMain = do
  mb_input  <- getInput "TRS"
  mb_visual <- getInput "LOG"
  mb_type   <- getInput "TYPE"
  mb_goal   <- getInput "GOAL" >>= \mb_g -> return(mb_g >>= \g -> let g' = filter (/= ' ') g in if null g' then Nothing else return g')
  mb_strat  <- getInput "STRAT"
  case (mb_input, mb_type) of
    (Just input, Just typ) -> do
       (success, dotsol, htmlsol) <- liftIO $  case typ of
                       "PROLOG" -> let input' = maybe input ((input ++) .( "\n%query: " ++)) mb_goal
                                   in  process(parseProlog input' >>= uncurry (stratSolver mb_strat))
                       "BASIC"  -> process(parseTRS BNarrowing input >>= narradarSolver :: ProblemProof Html BasicId)
                       "FULL"   -> process(parseTRS  Narrowing input >>= narradarSolver :: ProblemProof Html BasicId)
       proof_log <- liftIO$ withTempFile "/tmp" "narradar-log-" $ \fp h -> do
                      let fn = takeBaseName fp ++ ".pdf"
                      hPutStrLn h dotsol
                      hClose h
                      system (printf "dot -Tpdf %s -o /home/narradar/public_html/logs/%s" fp fn)
                      return ("See a visual log of the proof " +++
                                anchor ! [href ("logs/" ++ fn)] << "here")
       output$ renderHtml $
                 if success
                    then thediv ! [identifier "title"] << h3 << "Termination was proved succesfully." +++ p << proof_log +++ p << htmlsol
                    else thediv ! [identifier "title"] << h3 << "Termination could not be proved."    +++ p << proof_log +++ p << htmlsol
    _ -> outputError 100 "missing parameter" []

--process :: (Ord id, Show id, T id :<: f, TRSC f) => ProblemProofG id Html f -> IO (Bool, ProblemProof id f, Html)
process p = return (isJust mb_sol, pprDot sol, toHtml sol) where
    mb_sol = runProof p
    sol    = fromMaybe p mb_sol

--stratSolver :: () => Maybe String ->
stratSolver Nothing              typ = prologSolver  defOpts typ
stratSolver (Just "TYPEHEUone")  typ = prologSolverOne' defOpts (typeHeu typ) (typeHeu typ)
stratSolver (Just "TYPEHEU2one") typ = prologSolverOne' defOpts (typeHeu2 typ) (typeHeu typ)
stratSolver (Just "TYPEHEU")     typ = prologSolver' defOpts (typeHeu2 typ) (typeHeu typ)
stratSolver (Just "TYPEHEU2")    typ = prologSolver' defOpts (typeHeu2 typ) (typeHeu typ)
--stratSolver (Just "INN")      typ = prologSolver' (simpleHeu innermost) (typeHeu typ)