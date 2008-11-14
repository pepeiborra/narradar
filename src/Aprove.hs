{-# LANGUAGE OverloadedStrings #-}
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
import System.Process
import Text.Printf
import Text.XHtml
import Text.HTML.TagSoup

import Types
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
  return$ (if "proven" `elem` [ text | TagText text <- parseTags output] then success else Problem.fail)
                                    (External Aprove) prob (primHtml output)


aproveProc :: TRS.Ppr f => FilePath -> Problem f -> IO (ProblemProgress Html f)
aproveProc path prob@(Problem Rewriting trs dps) =
   withTempFile "ntt_temp.trs" $ \ problem_file h_problem_file -> do
              hPutStr h_problem_file (pprTPDB prob)
              hPutStr stderr ("solving the following problem with Aprove:\n" ++ pprTPDB prob)
              hClose h_problem_file
              (inp,out,err,pid) <- runInteractiveCommand (printf "%s %s 5" path problem_file)
              waitForProcess pid
              output            <- hGetContents out
              errors            <- hGetContents err
              unless (null errors) (error ("Aprove failed with the following error: \n" ++ errors))
              return$ (if take 3 output == "YES" then success else Problem.fail)
                        (External Aprove) prob (massage output)


aproveSrvTimeout = 10
aproveSrvProc :: TRS.Ppr f => Problem f -> IO (ProblemProgress Html f)
aproveSrvProc prob@(Problem Rewriting trs dps) = withSocketsDo $ withTempFile "ntt.trs" $ \fp0 h_problem_file -> do
    let trs = pprTPDB prob
    fp <- canonicalizePath fp0

    hPutStrLn stderr ("solving the following problem with Aprove:\n" ++ trs)
    hPutStr h_problem_file trs
    hFlush  h_problem_file
    hClose  h_problem_file

    hAprove <- connectTo "localhost" (PortNumber 5250)
  -- hSetBuffering hAprove NoBuffering
    hPutStrLn hAprove "2"                     -- Saying hello
    hPutStrLn hAprove fp                      -- Sending the problem path
    hPutStrLn hAprove (show aproveSrvTimeout) -- Sending the timeout
    hFlush hAprove
    res <- hGetContents hAprove

    let k = case (take 3 $ head $ lines res) of
              "YES" -> success
              _     -> Problem.fail
    evaluate (length res)
    hClose hAprove
    return (k (External Aprove) prob $ primHtml $ tail $ dropWhile (/= '\n') res)

withTempFile name m = bracket (openTempFile "." name) (removeFile . fst) (uncurry m)

massage    txt = (primHtml . unlines . drop 8  . lines . take (length txt - 9)) txt
massageWeb txt = (           unlines . drop 10 . lines . take (length txt - 9)) txt