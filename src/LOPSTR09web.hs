#!/usr/bin/env runhaskell
{-# LANGUAGE PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}

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

import Lattice
import Narradar hiding ((!))
import Narradar.Types hiding ((!))
import Narradar.Types.ArgumentFiltering (AF_, bestHeu)
import Narradar.Utils (eitherM, withTempFile)
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr as Ppr
import Narradar.Processor.Graph
import Narradar.Processor.GraphTransformation
import Narradar.Processor.LOPSTR09
import Narradar.Processor.RPO
import Narradar.Processor.RelativeProblem


web_pdf_folder   = "/~pepe/logs"

main :: IO ()
main = runCGI (handleErrors' cgiMain) -- (catchCGI cgiMain (output.show))
  where
    handleErrors' = (`catchCGI` \TimeoutException  -> output "Timeout").
                    (`catchCGI` \e@SomeException{} -> (output.show) e)

cgiMain :: CGI CGIResult
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

defPage :: MonadCGI m => m CGIResult
defPage = outputFPS (LBS.fromChunks [defaultForm])

solver = do
  mb_input <- getInput "TRS"
  timeout  <- (maybe 120 (min 120 . abs) . (>>= Safe.read)) <$> getInput "TIMEOUT"
  mypath <- fromMaybe "" <$> getInput "PATH"
  case mb_input of
    Just input -> do
       a_problem <- eitherM $ narradarParse "INPUT" input

       let proof   = dispatchAProblem a_problem      :: Proof (PrettyInfo, DotInfo) [] ()
       sol <- liftIO $ liftM Control.Monad.join $ withTimeout timeout $
              evaluate (listToMaybe (runProof proof) :: Maybe (Proof (PrettyInfo, DotInfo) [] ()))

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
                          proof_log <- mkProofLog
                          output$ renderHtml $
                            thediv ! [identifier "title"]
                             << [h3 << "Termination could not be proved."
                                ,p  << proof_log
                                ,pre << proof_txt
                                ]
                         `catchCGI` \TimeoutException -> output $ renderHtml $
                                                      h3 << "Termination could not be proved"

    _ -> outputError 100 "missing parameter" []

withTimeout t m = do
  res  <- newEmptyMVar
  done <- newMVar ()

  worker_id <- forkIO $ (`CE.catch` \TimeoutException -> return ()) $ do
             val <- m
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

-- ------------------------------
-- LOPSTR'09 Strategy hard-coded
-- ------------------------------

-- Prolog
instance Dispatch PrologProblem where
--    dispatch = apply SKTransformInfinitary >=> dispatch
    dispatch = apply SKTransformNarrowing >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = sc >=> rpoPlusTransforms >=> final

instance (id ~ DPIdentifier a, Pretty id, HasTrie id, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = sc >=> rpoPlusTransforms >=> final


-- Narrowing
instance Dispatch (NProblem Narrowing Id) where
  dispatch = apply DependencyGraphSCC >=> final -- rpoPlusTransforms >=> final

instance Dispatch (NProblem CNarrowing Id) where
  dispatch = rpoPlusTransforms >=> final


-- Narrowing Goal
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, HasTrie id) =>
    Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, HasTrie id) =>
    Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch

-- Infinitary
instance (HasTrie id, id  ~ DPIdentifier a, Ord a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) IRewriting) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply DependencyGraphSCC >=>
                 apply (InfinitaryToRewriting bestHeu True) >=>
                 dispatch)

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = sc >=> rpoPlusTransforms >=> final

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch = sc >=> rpoPlusTransforms >=> final

instance (Pretty (GenId id), Ord id, HasTrie id) =>
    Dispatch (NProblem (InitialGoal (TermF (GId id)) CNarrowingGen) (GId id)) where
  dispatch = rpoPlusTransforms >=> final

instance (Pretty (GenId id), Ord id, HasTrie id) =>
    Dispatch (NProblem (InitialGoal (TermF (GId id)) NarrowingGen) (GId id)) where
  dispatch = rpoPlusTransforms >=> final

-- Relative
instance (Dispatch (NProblem base id)
         ,Pretty id, Ord id, HasTrie id, Pretty (TermN id)
         ,IsDPProblem base, Pretty base, HasMinimality base
         ,MkProblem base (NTRS id)
         ,PprTPDB (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch


sc = apply DependencyGraphSCC >=> try SubtermCriterion

graphTransform = apply NarrowingP .|. apply FInstantiation .|. apply Instantiation

--rpoPlusTransforms ::
rpoPlusTransforms =  apply DependencyGraphSCC >=>
                         repeatSolver 3 (apply (RPOProc RPOSAF SMTFFI) .|. graphTransform >=>
                                         apply DependencyGraphSCC
                                        )

-- -------------------
-- Embedded content
-- -------------------

defaultForm = $(embedFile "resources/form.html")
defaultCss  = $(embedFile "style/narradar.css")