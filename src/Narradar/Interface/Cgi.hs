{-# LANGUAGE CPP #-}
{-# LANGUAGE OverlappingInstances, FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Interface.Cgi ( narradarCgi ) where

import Codec.Binary.Base64 as Base64
import Control.Applicative
import Control.Concurrent
import Control.Exception as CE (catch, evaluate,throw, throwTo, SomeException(..))
import Control.DeepSeq
import Control.Monad
import Control.Monad.Free
--import Control.OldException
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.FileEmbed
import Data.Foldable (Foldable,foldMap)
import Data.Maybe
import Data.Monoid
import Data.Traversable (Traversable)
import Network.CGI
import qualified Safe.Failure as Safe
import Text.Printf
import Text.XHtml hiding ((</>))
import Text.ParserCombinators.Parsec (runParser)

import System.Cmd
import System.Directory
import System.FilePath
import System.IO
--import System.IO.Error

import Prelude hiding (catch)

import Narradar hiding ((!))
import Narradar.Framework
import Narradar.Framework.GraphViz (dotProof', DotProof(..))
import Narradar.Utils
import MuTerm.Framework.Output

web_pdf_folder   = "/~pepe/logs"
defPage :: MonadCGI m => m CGIResult
defPage = outputFPS (LBS.fromChunks [defaultForm])

narradarCgi :: forall mp.
                 (IsMZero mp, Traversable mp
                 ,Dispatch (Problem Rewriting  (NTRS Id))
                 ,Dispatch (Problem IRewriting (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id)Rewriting) (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id)IRewriting) (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id) Narrowing)  (NTRS Id))
                 ,Dispatch (Problem (InitialGoal (TermF Id) INarrowing) (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) (InitialGoal (TermF Id) Rewriting))  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) (InitialGoal (TermF Id) IRewriting))  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) Rewriting)  (NTRS Id))
                 ,Dispatch (Problem (Relative  (NTRS Id) IRewriting)  (NTRS Id))
                 ,Dispatch (Problem Narrowing  (NTRS Id))
                 ,Dispatch (Problem CNarrowing (NTRS Id))
                 ,Dispatch PrologProblem
                 ) => (forall a. mp a -> Maybe a) -> IO ()
narradarCgi run = runCGI (handleErrors' cgiMain) where
 handleErrors' = (`catchCGI` \TimeoutException  -> output "Timeout").
                    (`catchCGI` \e@SomeException{} -> (output.show) e)

 cgiMain = do
  action <- getInput "action"
  tmp    <- liftIO$ getTemporaryDirectory
  case action of
    Just "getCss" -> outputFPS (LBS.fromChunks [defaultCss])
    Just "getPDF" -> do
            mb_file <- getInput "file"
            case mb_file of
              Nothing -> defPage
              Just f  -> do
                       setHeader "Content-type" "application/pdf"
                       outputFPS =<< liftIO(LBS.readFile (tmp </> f))
    Just "solve" -> solver
    _             -> defPage

 solver = do
  mb_input <- getInput "TRS"
  timeout  <- (maybe 120 (min 120 . abs) . (>>= Safe.read)) <$> getInput "TIMEOUT"
  mypath <- fromMaybe "" <$> getInput "PATH"
  case mb_input of
    Just input -> do
       a_problem <- eitherM $ narradarParse "INPUT" input

       let proof   = dispatchAProblem a_problem
       sol <- liftIO $ liftM Control.Monad.join $ withTimeout timeout $
              evaluate (run (runProof proof) :: Maybe(Proof PrettyDotF mp ()))

       let dotsol = case sol of
                       Just sol -> dotProof' DotProof{showFailedPaths = False} sol
                       Nothing  -> dotProof' DotProof{showFailedPaths = True} (sliceProof proof)

       tmp       <- liftIO$ getTemporaryDirectory
       let mkProofLog = do
              mb_log <- getInput "LOG"
              case mb_log of
                Nothing -> return noHtml
                Just _ -> liftIO $ withTempFile tmp "narradar-log-" $ \fp h -> do
                      let fn = takeBaseName fp ++ ".pdf"
                      hPutStrLn stderr "Calling dot"
                      hPutStrLn h dotsol
                      hClose h
                      system (printf "dot -Tpdf %s -o %s" fp (tmp </> fn))
                      pdfsrc <- (Base64.encode . BS.unpack) `liftM` BS.readFile (tmp </> fn)
                      return (False
                             ,p << [ toHtml "See a visual log of the proof "
                                   , anchor ! [href ("data:application/pdf;base64," ++ pdfsrc)] << "here"
                                   , toHtml " (or "
                                   , anchor ! [href (mypath ++ "?action=getPDF&file=" ++ fn)] << "here"
                                   , toHtml " if you have an underpowered web browser)"
                                   ]
                             )
       case sol of
                    Just sol -> do
                       proof_log <- mkProofLog
                       output$ renderHtml $
                         thediv ! [identifier "title"]
                           << [h3 << "Termination was proved succesfully."
                              ,p  << proof_log
                              ,pre  << sol]
                    _ -> do
                          proof_txt <- liftIO $ evaluate (pprProofFailures proof)
--                          proof_log <- mkProofLog
                          output$ renderHtml $
                            thediv ! [identifier "title"]
                             << [h3 << "Termination could not be proved."
--                                ,p  << proof_log
--                                ,pre << proof_txt
                                ]
                         `catchCGI` \TimeoutException -> output $ renderHtml $
                                                      h3 << "Termination could not be proved"

    _ -> outputError 100 "missing parameter" []

withTimeout t m = do
  res  <- newEmptyMVar
  done <- newMVar ()
  main_id <- myThreadId

  worker_id <- forkIO $ (`CE.catch` \TimeoutException -> return ())
                      $ (`CE.catch` \e@SomeException{} -> throwTo main_id e)
                      $ do val <- m
                           takeMVar done
                           putMVar res (Just val)

  clocker_id <- forkIO $ do
             threadDelay (t * 1000000)
             echo "time out"
             takeMVar done
             echo "signaled"
             CE.throwTo worker_id TimeoutException
             putMVar res Nothing
  takeMVar res

 where
  echo = hPutStrLn stderr

-- -------------------
-- Embedded content
-- -------------------

defaultForm = $(embedFile "resources/form.html")
defaultCss  = $(embedFile "style/narradar.css")