{-# LANGUAGE PackageImports, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
import Control.Applicative
import Control.OldException
import qualified "monad-param" Control.Monad.Parameterized as P
import Data.Foldable (Foldable,foldMap)
import Data.Maybe
import Data.Monoid
import Network.CGI
import TRS.FetchRules
import TRS.FetchRules.TRS
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
                       "NARROWING"  -> process(parseTRS (narrStrat strat mb_goal) input >>=
                                       narradarSolver :: ProblemProofG Id BasicId)
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
    mb_sol = runProof' iprob  `asTypeOf` Just iprob
    iprob  = improve p
    sol    = fromMaybe iprob mb_sol

narrStrat "FULL"  Nothing = Narrowing
narrStrat "FULL" (Just g_) = let gg = either (error.show) id $ parseGoal g_
                            in let g_af = foldMap mkGoalAF gg in NarrowingModes g_af g_af
{-
narrStrat "BASIC"  Nothing = BNarrowing
narrStrat "BASIC" (Just g_) = let g = either (error.show) id $ parseT trsParser "<goal>" g_
                            in BNarrowingModes g
narrStrat "CONSTRUCTOR"  Nothing = GNarrowing
narrStrat "CONSTRUCTOR" (Just g_) = let g = either (error.show) id $ parseT trsParser "<goal>" g_
                            in GNarrowingModes g
-}

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
instance (T id :<: f, IsU1Id id, Ord id, Foldable f) => PolyHeuristic IsU1 id f where
  runPolyHeu (IsU1 sig) =  Heuristic (predHeuOne allOuter noU1s `AF.or` predHeuOne allOuter (noConstructors sig)) False
    where noU1s _af (t, 1) = not$ isU1Id t
          noU1s _ _ = True

class IsU1Id id where isU1Id :: id -> Bool
instance IsU1Id PId where isU1Id (symbol -> UId{}) = True; isU1Id _ = False
instance IsU1Id PS  where isU1Id (UId{}) = True; isU1Id _ = False
instance IsU1Id LPS where isU1Id (unlabel -> UId{}) = True; isU1Id _ = False
instance IsU1Id LPId where isU1Id (unlabel.symbol -> UId{}) = True; isU1Id _ = False
