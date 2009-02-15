{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Aprove where

import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.List
import Network
import Network.Curl
import System.Directory
import System.FilePath
import System.IO
import System.IO.Unsafe
import System.Process
import Text.Printf
import Text.XHtml hiding ((</>))
import Text.HTML.TagSoup

import Types
import Output
import Proof
import TRS
import Utils


aproveWebProc :: (Bottom :<: f, Show id, DPSymbol id) => ProblemG id f -> IO (ProblemProofG id Html f)
aproveWebProc = externalProc go where
  go prob@(Problem _ trs dps@TRS{}) = do
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
--    hPutStrLn stderr ("asking aprove to solve the following problem\n" ++ pprTPDB prob)
    response :: CurlResponse <- perform_with_response curl
    let output = massageWeb $ respBody response
    return$ (if "proven" `elem` [ text | TagText text <- parseTags output] then success else failP)
            (External$ Aprove "WEB") prob (primHtml output)

aproveProc :: (TRS.Ppr f, Bottom :<: f, Show id, DPSymbol id) => FilePath -> ProblemG id f -> IO (ProblemProofG id Html f)
aproveProc path = externalProc go where
   go prob@(Problem Rewriting trs dps) =
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

aproveSrvTimeout = 10
aproveSrvPort    = 5250

aproveSrvProc :: (Bottom :<: f, TRS.Ppr f, Show id, DPSymbol id) => ProblemG id f -> IO (ProblemProofG id Html f)
{-# SPECIALIZE aproveSrvProc :: Problem BBasicId -> IO (ProblemProof Html BBasicId) #-}
aproveSrvProc = externalProc go where
  go prob@(Problem Rewriting trs dps) = unsafeInterleaveIO $
                                                 withSocketsDo $
                                                 withTempFile "/tmp" "ntt.trs" $ \fp0 h_problem_file -> do
    let trs = pprTPDB prob
    let fp = "/tmp" </> fp0

--    hPutStrLn stderr ("solving the following problem with Aprove:\n" ++ trs)
    hPutStr h_problem_file trs
    hFlush  h_problem_file
    hClose  h_problem_file
--    runCommand ("chmod o+r " ++ fp)

    hAprove <- connectTo "127.0.0.1" (PortNumber aproveSrvPort)
  -- hSetBuffering hAprove NoBuffering
    hPutStrLn hAprove "2"                     -- Saying hello
    hPutStrLn hAprove fp                      -- Sending the problem path
    hPutStrLn hAprove (show aproveSrvTimeout) -- Sending the timeout
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


externalProc go p@(Problem (isRewriting -> True) trs dps@TRS{}) = unsafePerformIO (memoIO hashProb go) p
externalProc _ p = return$ return p

hashProb prob = hashString (pprTPDB prob)
massage    txt = (primHtml . unlines . drop 8  . lines . take (length txt - 9)) txt
massageWeb txt = (           unlines . drop 10 . lines . take (length txt - 9)) txt