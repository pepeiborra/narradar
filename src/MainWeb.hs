{-# LANGUAGE PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
import Control.Applicative
import Control.Monad
import Control.OldException
import Data.Foldable (Foldable,foldMap)
import Data.Maybe
import Data.Monoid
import Network.CGI
import Text.Printf
import Text.XHtml
import Text.ParserCombinators.Parsec (parse)

import System.Cmd
import System.FilePath
import System.IO
import System.IO.Error

import Prelude

import Narradar hiding ((!))
import Narradar.ArgumentFiltering as AF
import Narradar.PrologIdentifiers
import Narradar.Solver
import Narradar.Output
import Narradar.Proof
import Narradar.Utils (withTempFile)
import Narradar.GraphViz

main = runCGI (catchCGI cgiMain (output.showExcep)) where
  showExcep (ErrorCall msg) = msg
  showExcep (IOException ie)
   | isUserError ie = show ie
   | otherwise      = ioeGetErrorString ie
  showExcep e = show e

cgiMain = do
  mb_input  <- getInput "TRS"
  mb_visual <- getInput "LOG"
  mb_type   <- getInput "TYPE"
  mb_strat  <- getInput "STRAT"
  mb_goal   <- getInput "GOAL" >>= \mb_g -> return(mb_g >>= \g ->
                                            let g' = takeWhile (/= ' ') g in if null g' then Nothing else return g')
  case (mb_input, mb_type, mb_strat) of
    (Just input, Just typ, Just strat) -> do
       (success, dotsol, htmlsol) <- liftIO $  case typ of
                       "LOGIC" -> let input' = maybe input ((input ++) .( "\n%query: " ++)) mb_goal
                                   in  process(parseProlog input' >>= uncurry (stratSolver mb_strat))
                       "NARROWING"  -> let input' = Prelude.unlines [input, narrStrat strat mb_goal]  in
                                       process(parseTRS input' >>= narradarSolver)
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
    mb_sol = runProof' iprob `asTypeOf` Just iprob
    iprob  = improve p
    sol    = fromMaybe iprob mb_sol

narrStrat "FULL"  Nothing  = "(STRATEGY NARROWING)"
narrStrat "FULL" (Just g_) = "(STRATEGY NARROWING " ++ g_ ++ ")"
narrStrat "BASIC"  Nothing  = "(STRATEGY BASICNARROWING)"
narrStrat "BASIC" (Just g_) = "(STRATEGY BASICNARROWING " ++ g_ ++ ")"

--stratSolver :: () => Maybe String ->
stratSolver Nothing              typ = prologSolver  defOpts typ
stratSolver (Just "TYPEHEUone")  typ = prologSolverOne' defOpts (typeHeu typ) (typeHeu typ)
stratSolver (Just "TYPEHEU2one") typ = prologSolverOne' defOpts (typeHeu2 typ) (typeHeu typ)
stratSolver (Just "TYPEHEU")     typ = prologSolver' defOpts (typeHeu2 typ) (typeHeu typ)
stratSolver (Just "TYPEHEU2")    typ = prologSolver' defOpts (typeHeu2 typ) (typeHeu typ)
stratSolver (Just "INN")         typ = prologSolver' defOpts (simpleHeu innermost) (typeHeu typ)
stratSolver (Just "OUT")         typ = prologSolver' defOpts (simpleHeu outermost) (typeHeu typ)
stratSolver (Just "OUTU1")       typ = prologSolver' defOpts noU1sHeu (typeHeu typ)
--stratSolver (Just "INN")      typ = prologSolver' (simpleHeu innermost) (typeHeu typ)



-- No U1s Heuristic
-- ----------------
noU1sHeu = MkHeu (IsU1 . getSignature)

data IsU1 id (f :: * -> *) = IsU1 (Signature id)
instance (IsPrologId id, Ord id, HasId f id, Foldable f) => PolyHeuristic IsU1 id f where
  runPolyHeu (IsU1 sig) =
      Heuristic (predHeuOne allOuter noU1s `AF.or`
                 predHeuOne allOuter (noConstructors sig))
                False
    where noU1s _af (t, 1) = not$ isUId t
          noU1s _ _ = True
