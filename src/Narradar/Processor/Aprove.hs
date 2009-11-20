{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards, RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Processor.Aprove where

import Control.Applicative hiding ((<|>), many)
import Control.Exception
import Control.Monad
import Data.ByteString.Char8 as BS (pack, unpack)
import Data.Char
import Data.Foldable  (toList, Foldable)
import Data.HashTable (hashString)
import Data.List
import Data.Maybe
import Data.Monoid
import Network
-- import Network.Curl hiding (Info)
import System.FilePath
import System.IO
import System.IO.Unsafe
import System.Process
import Text.Printf
import Text.XHtml (HTML(..), primHtml)
import Text.HTML.TagSoup
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Tag

import Paths_narradar

import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Types hiding ((!),(.|.), (.&.), PprTPDB(..))
import Narradar.Types.Problem.Rewriting
import Narradar.Utils (withTempFile, memoIO, eitherM, tailSafe, (.|.), (.&.))
import Narradar.Utils.Html

--type ExternalProcTyp proof id v = (Ord id, Ppr id, Ord v, Enum v, Ppr v, MonadFree ProofF proof) => Problem id v -> IO (proof(Problem id v))

-- -----------------
-- Aprove Processor
-- -----------------

data Aprove = AproveServer {timeout :: Seconds, strategy :: Strat}
            | AproveWeb
            | AproveBinary {path :: FilePath}
              deriving (Show, Eq)

type Seconds = Int
data Strat   = Default | OnlyReductionPair deriving (Show, Eq)

strats = [ (Default,           "aproveStrats/narradar.strategy")
         , (OnlyReductionPair, "aproveStrats/reductionPair.strategy")]

stratFor s = Data.Maybe.fromJust (Prelude.lookup s strats)

aprove = apply (AproveServer 10 Default)

-- ---------------
-- Aprove proofs
-- ---------------

data AproveProof = AproveProof [Output]
instance Pretty AproveProof  where pPrint   (AproveProof outs) = text "Aprove:" <+> vcat [ text(BS.unpack txt) | OutputTxt txt <- outs]

instance HTML AproveProof where
 toHtml (AproveProof outputs)
     | Just (OutputHtml html) <- find isOutputHtml outputs = thickbox (unpack html) << spani "seeproof" << "(see proof)"

-- ------------------
-- Allowed instances
-- ------------------
instance ( p ~ Problem Rewriting trs
         , PprTPDB p, Eq trs, Pretty trs, HasRules t v trs, Pretty (t(Term t v))
         , Info info AproveProof
         ) =>
    Processor info Aprove (Problem Rewriting trs) (Problem Rewriting trs)
  where
    apply AproveWeb{..}    = unsafePerformIO . aproveWebProc
    apply AproveBinary{..} = unsafePerformIO . aproveProc path
    apply AproveServer{..} = unsafePerformIO . aproveSrvProc2 strategy timeout

instance ( p ~ Problem IRewriting trs
         , PprTPDB p, Eq trs, Pretty trs, HasRules t v trs, Pretty (t(Term t v))
         , Info info AproveProof
         ) =>
    Processor info Aprove (Problem IRewriting trs) (Problem IRewriting trs)
  where
    apply AproveWeb{..} = unsafePerformIO . aproveWebProc
    apply AproveBinary{..} = unsafePerformIO . aproveProc path
    apply AproveServer{..} = unsafePerformIO . aproveSrvProc2 strategy timeout

instance ( Info info (Problem i trs)
         , Processor info Aprove (Problem i trs) o
         ) =>
    Processor info Aprove (Problem (InitialGoal t i) trs) o where
    apply mode InitialGoalProblem{..} = apply mode baseProblem

-- ------------------
-- Implementation
-- ------------------

aproveWebProc = error "unsupported in Snow Leopard"
{-
aproveWebProc :: ( p ~ Problem typ trs
                 , IsDPProblem typ, Eq p, PprTPDB p
                 , HasRules t v trs, Pretty (t(Term t v))
                 , Info info p, Info info AproveProof
                 , Monad mp
                 ) => p -> IO (Proof info mp b)
aproveWebProc = memoExternalProc go where
  go prob = do
    curl <- initialize
    let source = show(pprTPDB prob)
    CurlOK <- setopt curl (CurlURL "http://aprove.informatik.rwth-aachen.de/index.asp?subform=termination_proofs.html")
    CurlOK <- setopt curl (CurlHttpPost [multiformString "subform" "termination_proofs.html"
                                      ,multiformString "program_type" "trs"
                                      ,multiformString "source" source
                                      ,multiformString "timeout" "10"
                                      ,multiformString "head" "no"
                                      ,multiformString "output" "html"
                                      ,multiformString "submit_mode" "Submit"
                                      ,multiformString "fullscreen_request" "1"])
#ifdef DEBUG
    hPutStrLn stderr ("sending the following problem to aProve web interface \n" ++ source)
#endif
    response :: CurlResponse <- perform_with_response_ curl
    let output = respBody response
    return$ (if isTerminating output then success else dontKnow)
            (AproveProof [OutputHtml  (pack output)]) prob
-}
isTerminating (canonicalizeTags.parseTags -> tags) = let
     ww = words $ map toLower $ innerText $ takeWhile ((~/= "<br>") .&. (~/= "</p>")) $ dropWhile (~/= "<b>") $ dropWhile (~/= "<body>") tags
  in any (("termination" `isPrefixOf`) .|. ("finiteness" `isPrefixOf`)) ww &&
     any ("proven" `isPrefixOf`) ww && ("not" `notElem` ww)


--aproveProc :: FilePath -> ExternalProcTyp m id v
aproveProc path = go where
   go prob =
     withTempFile "/tmp" "ntt_temp.trs" $ \ problem_file h_problem_file -> do
              let source = show $ pprTPDB prob
              hPutStr h_problem_file source
              hPutStr stderr ("solving the following problem with Aprove:\n" ++ source)
              hClose h_problem_file
              (_,out,err,pid) <- runInteractiveCommand (printf "%s %s 5" path problem_file)
              waitForProcess pid
              output            <- hGetContents out
              errors            <- hGetContents err
              unless (null errors) (error ("Aprove failed with the following error: \n" ++ errors))
              return$ (if take 3 output == "YES" then success else dontKnow)
                        (AproveProof [OutputHtml(pack $ massage output)] ) prob

aproveSrvPort    = 5250

{-
aproveSrvProc :: (Ord id, Show id,TRSC f, T id :<: f) => Int -> Problem id f -> IO (ProblemProofG id Html f)
{-# SPECIALIZE aproveSrvProc :: Int -> Problem BBasicId -> IO (ProblemProof Html BBasicId) #-}
aproveSrvProc timeout =  go where
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
              _     -> dontKnow
    evaluate (length res)
    hClose hAprove
    return (k (External $ Aprove "SRV") prob $ primHtml $ tail $ dropWhile (/= '\n') res)
    where headSafe err [] = error ("head: " ++ err)
          headSafe _   x  = head x

-}

callAproveSrv s t p = memoCallAproveSrv'(s,t,p)
{-# NOINLINE memoCallAproveSrv' #-}
memoCallAproveSrv' = unsafePerformIO (memoIO (hashString . show) callAproveSrv')

callAproveSrv' :: (Strat,Int, String) -> IO String
callAproveSrv' (strat, timeout, p) = withSocketsDo $ withTempFile "/tmp" "ntt.trs" $ \fp0 h_problem_file -> do
    let fp = "/tmp" </> fp0
#ifdef DEBUG
    hPutStrLn stderr ("solving the following problem with Aprove:\n" ++ p)
#endif
    hPutStr h_problem_file p
    hFlush  h_problem_file
    hClose  h_problem_file
    hAprove <- connectTo "127.0.0.1" (PortNumber aproveSrvPort)

    hPutStrLn hAprove "3"                     -- Saying hello
    hPutStrLn hAprove fp                      -- Sending the problem path
    hPutStrLn hAprove =<< getDataFileName (stratFor strat) -- strategy file path

    hPutStrLn hAprove (show timeout) -- Sending the timeout
    hFlush hAprove
    res <- hGetContents hAprove
    evaluate (length res)
    hClose hAprove
    return res

aproveSrvXML strat (timeout :: Int) prob =
    let p = show(pprTPDB prob) in callAproveSrv strat timeout p

aproveSrvProc2 strat (timeout :: Int) =  go where
  go prob = do
    res <- aproveSrvXML strat timeout prob
    let k = case (take 3 $ headSafe "Aprove returned NULL" $ lines res) of
              "YES" -> success
              _     -> dontKnow
    return (k (AproveProof [OutputXml (pack $ tail $ dropWhile (/= '\n') res)]) prob)
    where headSafe err [] = error ("head: " ++ err)
          headSafe _   x  = head x
  go p = return $ return p

{-# NOINLINE memoExternalProc #-}
memoExternalProc go = unsafePerformIO (memoIO hashProb go)


hashProb prob = hashString (show $ pprTPDB prob)
massage     = unlines . drop 8  . lines

-- ----
-- TPDB
-- ----

class PprTPDB p where pprTPDB :: p -> Doc

instance (GetVars v trs, HasRules t v trs
         ,Pretty (t(Term t v)), Pretty v, Enum v, Foldable t, HasId t, Pretty (TermId t)
         ) => PprTPDB (Problem Rewriting trs) where
 pprTPDB p =
     vcat [ parens (text "VAR" <+> hsep (map pprVar (toList $ getVars p)))
          , parens (text "PAIRS" $$
                    vcat (map pprRule (rules $ getP p)))
          , parens (text "RULES" $$
                    vcat (map pprRule (rules $ getR p)))
          ]
  where pprRule (a:->b) = pprTerm a <+> text "->" <+> pprTerm b
        pprVar v = text "v" <> int(fromEnum v)
        pprTerm  = foldTerm pprVar f
--        f (prj -> Just (T (id::id) [])) = text (show id)
        f t | Just id <- getId t
            , show (pPrint id) == "','"
            = text "comma" <> parens (hcat$ punctuate comma $ toList t) -- TODO Fix this HACK
            | Just id <- getId t
            = pPrint id <> parens (hcat$ punctuate comma $ toList t)

-- TODO Relative Termination

instance (GetVars v trs, HasRules t v trs, Monoid trs, MkDPProblem Rewriting trs
         ,Pretty (t(Term t v)), Pretty v, Enum v, Foldable t, HasId t, Pretty (TermId t)
         ) => PprTPDB (Problem IRewriting trs) where
 pprTPDB p = pprTPDB (mkDerivedDPProblem rewriting p) $$ text "(STRATEGY INNERMOST)"

-- ----------------
-- Parse XML
-- ----------------
findResultingPairs :: String -> Maybe [RuleN String]
findResultingPairs x = (eitherM . parse proofP "" . parseTags . dropLine) x
  where dropLine = tailSafe . dropWhile (/= '\n')

proofP = tag "<?xml>" >>
       (
         someTagP "<proof-obligation>" $
         someTagP "<proposition>" $ do
          skipTagNameP "<basic-obligation>"
          tagP "<proof>" (skipTagNameP "<qdp-reduction-pair-proof>")
          skipTagNameP "<implication value='equivalent'>"
          tagP "<proof-obligation>" $
           tagP "<proposition>" $
           tagP "<basic-obligation>" $
           tagP "<qdp-termination-obligation>" $
           tagP "<qdp>" $
           someTagP "<dps>" $ do
                            dps <- many (do {r<-ruleP;return[r]} <|> do{skipTagP;return[]})
                            return (concat dps)
       )

ruleP = tokenP(tagP "<rule>" ((:->) <$> (skipMany tagText >> termP) <*> termP))
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
