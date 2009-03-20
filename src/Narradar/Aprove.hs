{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Narradar.Aprove where

import Control.Applicative hiding ((<|>), many)
import Control.Arrow ((>>>))
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.Char
import Data.HashTable (hashString)
import Data.List
import Data.Maybe
import Network
import Network.Curl
import System.Directory
import System.FilePath
import System.IO
import System.IO.Unsafe
import System.Process
import Text.PrettyPrint (parens, text ,hcat, punctuate, comma, (<>), (<+>))
import Text.Printf
import Text.XHtml (Html, primHtml, toHtml)
import Text.HTML.TagSoup
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Tag

import Paths_narradar

import TRS
import Narradar.Types
import Narradar.Output
import Narradar.Proof
import Narradar.Utils

aproveWebProc :: (Ord id, Show id, TRSC f, T id :<: f) => ProblemG id f -> IO (ProblemProofG id Html f)
aproveWebProc = memoExternalProc go where
  go prob@(Problem  (isRewriting -> True) trs dps) = do
    curl <- initialize
    CurlOK <- setopt curl (CurlURL "http://aprove.informatik.rwth-aachen.de/index.asp?subform=termination_proofs.html")
    CurlOK <- setopt curl (CurlHttpPost [multiformString "subform" "termination_proofs.html",
                                       multiformString "program_type" "trs"
                                      ,multiformString "source" (pprTPDB prob)
                                      ,multiformString "timeout" "10"
                                      ,multiformString "head" "no"
                                      ,multiformString "output" "html"
                                      ,multiformString "submit_mode" "Submit"
                                      ,multiformString "fullscreen_request" "1"])
#ifdef DEBUG
    hPutStrLn stderr ("sending the following problem to aProve web interface \n" ++ pprTPDB prob)
#endif
    response :: CurlResponse <- perform_with_response curl
    let output = respBody response
    return$ (if isTerminating output then success else failP)
            (External$ Aprove "WEB") prob (primHtml output)

isTerminating (canonicalizeTags.parseTags -> tags) = let
     ww = words $ map toLower $ innerText $ takeWhile ((~/= "<br>") .&. (~/= "</p>")) $ dropWhile (~/= "<b>") $ dropWhile (~/= "<body>") tags
  in any (("termination" `isPrefixOf`) .|. ("finiteness" `isPrefixOf`)) ww &&
     any ("proven" `isPrefixOf`) ww && ("not" `notElem` ww)


aproveProc :: (Ord id, Show id, TRSC f, T id :<: f) => FilePath -> ProblemG id f -> IO (ProblemProofG id Html f)
aproveProc path = go where
   go prob@(Problem (isRewriting -> True) trs dps) =
     withTempFile "/tmp" "ntt_temp.trs" $ \ problem_file h_problem_file -> do
              hPutStr h_problem_file (pprTPDB prob)
              hPutStr stderr ("solving the following problem with Aprove:\n" ++ pprTPDB prob)
              hClose h_problem_file
              (inp,out,err,pid) <- runInteractiveCommand (printf "%s %s 5" path problem_file)
              waitForProcess pid
              output            <- hGetContents out
              errors            <- hGetContents err
              unless (null errors) (error ("Aprove failed with the following error: \n" ++ errors))
              return$ (if take 3 output == "YES" then success else failP)
                        (External $ Aprove path) prob (massage output)

aproveSrvPort    = 5250

aproveSrvProc :: (Ord id, Show id,TRSC f, T id :<: f) => Int -> ProblemG id f -> IO (ProblemProofG id Html f)
{-# SPECIALIZE aproveSrvProc :: Int -> Problem BBasicId -> IO (ProblemProof Html BBasicId) #-}
aproveSrvProc timeout = memoExternalProc go where
  go prob@(Problem  (isRewriting -> True) trs dps) = unsafeInterleaveIO $
                                                 withSocketsDo $
                                                 withTempFile "/tmp" "ntt.trs" $ \fp0 h_problem_file -> do
    let trs = pprTPDB prob
    let fp = "/tmp" </> fp0

#ifdef DEBUG
    hPutStrLn stderr ("solving the following problem with Aprove:\n" ++ trs)
#endif
    hPutStr h_problem_file trs
    hFlush  h_problem_file
    hClose  h_problem_file
--    runCommand ("chmod o+r " ++ fp)

    hAprove <- connectTo "127.0.0.1" (PortNumber aproveSrvPort)
 -- hSetBuffering hAprove NoBuffering
    hPutStrLn hAprove "2"                     -- Saying hello
    hPutStrLn hAprove fp                      -- Sending the problem path
    hPutStrLn hAprove (show timeout) -- Sending the timeout
    hFlush hAprove
    res <- hGetContents hAprove

    let k = case (take 3 $ headSafe "Aprove returned NULL" $ lines res) of
              "YES" -> success
              _     -> failP
    evaluate (length res)
    hClose hAprove
    return (k (External $ Aprove "SRV") prob $ primHtml $ tail $ dropWhile (/= '\n') res)
    where headSafe err [] = error ("head: " ++ err)
          headSafe _   x  = head x


data Strat = Default | OnlyReductionPair deriving Eq

strats = [ (Default,           "aproveStrats/narradar.strategy")
         , (OnlyReductionPair, "aproveStrats/reductionPair.strategy")]

aproveSrvXML strat (timeout :: Int) prob@(Problem  (isRewriting -> True) trs dps) =
  withSocketsDo $ withTempFile "/tmp" "ntt.trs" $ \fp0 h_problem_file -> do
    let trs = pprTPDB prob
    let fp = "/tmp" </> fp0
#ifdef DEBUG
    hPutStrLn stderr ("solving the following problem with Aprove:\n" ++ trs)
#endif
    hPutStr h_problem_file trs
    hFlush  h_problem_file
    hClose  h_problem_file

    hAprove <- connectTo "127.0.0.1" (PortNumber aproveSrvPort)

    hPutStrLn hAprove "3"                     -- Saying hello
    hPutStrLn hAprove fp                      -- Sending the problem path
    hPutStrLn hAprove =<< getDataFileName (Data.Maybe.fromJust (Prelude.lookup strat strats))

    hPutStrLn hAprove (show timeout) -- Sending the timeout
    hFlush hAprove
    res <- hGetContents hAprove
    evaluate (length res)
    hClose hAprove
    return res
    where headSafe err [] = error ("head: " ++ err)
          headSafe _   x  = head x

aproveSrvProc2 strat (timeout :: Int) =  go where
  go prob@(Problem  (isRewriting -> True) trs dps) = do
    res <- aproveSrvXML strat timeout prob
    let k = case (take 3 $ headSafe "Aprove returned NULL" $ lines res) of
              "YES" -> success
              _     -> failP
    return (k (External $ Aprove "SRV") prob $ primHtml $ tail $ dropWhile (/= '\n') res)
    where headSafe err [] = error ("head: " ++ err)
          headSafe _   x  = head x

{-# NOINLINE memoExternalProc #-}
memoExternalProc go = unsafePerformIO (memoIO hashProb go)


hashProb prob = hashString (pprTPDB prob)
massage     = primHtml . unlines . drop 8  . lines

-- ----
-- TPDB
-- ----

pprTPDB :: forall f id. (Show id, Ord id, TRSC f, T id :<: f) => ProblemG id f -> String
pprTPDB p@(Problem typ trs dps) =
  unlines ([ printf "(VAR %s)" (unwords $ map (show . pprTerm) $ snub $ foldMap3 vars' ( rules <$> p))
           , printf "(PAIRS\n %s)" (unlines (map (show.pprRule) (rules dps)))
           , printf "(RULES\n %s)" (unlines (map (show.pprRule) (rules trs)))
           ] ++ if (isInnermostRewriting typ) then ["(STRATEGY INNERMOST)"] else [])

  where pprRule (a:->b) = pprTerm a <+> text "->" <+> pprTerm b
        pprTerm = foldTerm f
        f (prj -> Just (Var i n))       = TRS.ppr (var n :: Term f)
        f (prj -> Just (T (id::id) [])) = text (show id)
        f (prj -> Just (T (id::id) tt)) =
            text (show id) <> parens (hcat$ punctuate comma tt)
        f t = pprF t
{-
        f (prj -> Just Bottom) =  -- TODO Cache the obtained representation on first call
            text $ fromJust $ find (not . flip Set.member (allSymbols$getSignature p) . functionSymbol)
                                   ("_|_":["_|_"++show i | i <- [0..]])
-}

-- ----------------
-- Parse XML
-- ----------------

findResultingPairs = dropWhile (~/= "<qdp-reduction-pair-proof>")
                 >>> dropWhile (~/= "<implication value='equivalent'>")
                 >>> dropWhile (~/= "<dps>")
                 >>> (tailSafe >=> (eitherM . parse (many ruleP) ""))
  where tailSafe []     = Nothing
        tailSafe (_:xx) = Just xx

ruleP = skipMany tagText >> tokenP(tagP "<rule>" ((:->) <$> (skipMany tagText >> termP) <*> termP))
termP = tokenP(tagP "<term>" (skipMany tagText >> (funAppP <|> variableP)))
funAppP = tokenP $ tagP "<fun-app>" $ do
            skipMany tagText
            symb_tag <- tokenP (tag "<symbol>" <* tag "</symbol>")
            tt       <- many termP
            skipMany tagText
            let symb  = fromAttrib "name" symb_tag
            return (term symb tt)

-- Only works for Narradar, assumes a term given to AproVE by Narradar
variableP = tokenP ((mkVar <$> tag "<variable>") <* tag "</variable>") where
      mkVar tag = let symb = fromAttrib "name" tag
                  in  var' (Just symb) (read $ tail symb)

tokenP p = p <* skipMany tagText