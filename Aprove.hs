{-# LANGUAGE OverloadedStrings #-}
module Aprove where

import Control.Exception
import qualified Data.ByteString as B
import Data.List
import Network.Curl
import System.Directory
import System.IO
import System.Process
import Text.Printf
import Text.XHtml
import Text.HTML.TagSoup

import Problem
import TRS

aproveWebProc :: TRS.Ppr f => Problem f -> IO (ProblemProgress Html f)
aproveWebProc prob@(Problem Rewriting trs dps) = withCurlDo $ do
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
  hPutStrLn stderr ("asking aprove to solve the following problem\n" ++ pprTPDB prob)
  response <- perform_with_response curl
  let output = massageWeb $ respBody response
  return$ (if "proven" `elem` [ text | TagText text <- parseTags output] then Success else Fail)
                                    (External Aprove) prob (primHtml output)


aproveProc :: TRS.Ppr f => FilePath -> Problem f -> IO (ProblemProgress Html f)
aproveProc path prob@(Problem Rewriting trs dps) =
   bracket (openTempFile "." "ntt_temp.trs")
           (removeFile . fst)
           (\(problem_file,h_problem_file) -> do
              hPutStr h_problem_file (pprTPDB prob)
              hPutStr stderr (pprTPDB prob)
              hClose h_problem_file
              (inp,out,err,pid) <- runInteractiveCommand (printf "%s %s 5" path problem_file)
              waitForProcess pid
              output            <- hGetContents out
              return$ (if take 3 output == "YES" then Success else Fail)
                                    (External Aprove) prob (massage output))

massage txt = primHtml . unlines . drop 8 . lines . take (length txt - 9) $ txt
massageWeb txt = unlines . drop 10 . lines . take (length txt - 9) $ txt