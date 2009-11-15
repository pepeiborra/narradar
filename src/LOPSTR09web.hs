#!/usr/bin/env runhaskell
{-# LANGUAGE PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}

import Control.Applicative
import Control.Monad
import Control.OldException
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.FileEmbed
import Data.Foldable (Foldable,foldMap)
import Data.Maybe
import Data.Monoid
import Network.CGI
import Text.Printf
import Text.XHtml hiding ((</>))
import Text.ParserCombinators.Parsec (runParser)

import System.Cmd
import System.Directory
import System.FilePath
import System.IO
import System.IO.Error

import Prelude

import Lattice
import Narradar hiding ((!))
import Narradar.Types hiding ((!))
import Narradar.Types.ArgumentFiltering (AF_, bestHeu)
import Narradar.Utils (eitherM, withTempFile)
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Processor.Graph
import Narradar.Processor.GraphTransformation
import Narradar.Processor.RPO
import Narradar.Processor.InitialGoalNarrowingProblem
import Narradar.Processor.RelativeProblem

web_pdf_folder   = "/~pepe/logs"

main :: IO ()
main = runCGI (handleErrors cgiMain) -- (catchCGI cgiMain (output.show))

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
  mb_input  <- getInput "TRS"
  case (mb_input) of
    Just input -> do
       a_problem <- eitherM $ narradarParse "INPUT" input

       let proof   = dispatchAProblem a_problem   :: Proof (PrettyInfo, DotInfo) [] ()
           sol     = listToMaybe (runProof proof) :: Maybe (Proof (PrettyInfo, DotInfo) [] ())
           dotsol  = case sol of
                       Just sol -> dotProof' DotProof{showFailedPaths = True} sol
                       Nothing  -> dotProof' DotProof{showFailedPaths = True} (sliceWorkDone proof)

       tmp       <- liftIO$ getTemporaryDirectory
       proof_log <- liftIO$ withTempFile tmp "narradar-log-" $ \fp h -> do
                      let fn = takeBaseName fp ++ ".pdf"
                      hPutStrLn h dotsol
                      hClose h
                      system (printf "dot -Tpdf %s -o %s" fp (tmp </> fn))
                      return ("See a visual log of the proof " +++
                                anchor ! [href ("?action=getPDF&file=" ++ fn)] << "here")
       output$ renderHtml $
                 case sol of
                    Just sol ->
                         thediv ! [identifier "title"]
                           << [h3 << "Termination was proved succesfully."
                              ,p  << proof_log
                              ,p  << sol]
                    _ -> thediv ! [identifier "title"]
                             << [h3 << "Termination could not be proved."
                                ,p  << proof_log
                                ]

    _ -> outputError 100 "missing parameter" []

-- ------------------------------
-- LOPSTR'09 Strategy hard-coded
-- ------------------------------

-- Prolog
instance Dispatch PrologProblem where
--    dispatch = apply SKTransformInfinitary >=> dispatch
    dispatch = apply SKTransformNarrowing >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

instance (id ~ DPIdentifier a, Pretty id, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

-- Narrowing
instance (Pretty id, Pretty (DPIdentifier id), Ord id, Lattice (AF_ (DPIdentifier id))) =>
    Dispatch (NProblem Narrowing (DPIdentifier id)) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

instance (Pretty id, Pretty (DPIdentifier id), Ord id, Lattice (AF_ (DPIdentifier id))) =>
   Dispatch (NProblem CNarrowing (DPIdentifier id)) where
--  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)
  dispatch = mkDispatcher (apply DependencyGraphSCC >=>
                            (apply (RPOProc LPOSAF Yices) .|. (apply Instantiation .|. apply FInstantiation))
                          )

-- Narrowing Goal
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id) => Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id) => Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch

-- Infinitary
instance (id  ~ DPIdentifier a, Ord a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) IRewriting) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply DependencyGraphSCC >=>
                 apply (InfinitaryToRewriting bestHeu) >=>
                 dispatch)

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

instance (Pretty (GenId id), Ord id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) CNarrowingGen) (GId id)) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

instance (Pretty (GenId id), Ord id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) NarrowingGen) (GId id)) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

-- Relative
instance (Dispatch (NProblem base id)
         ,Pretty id, Ord id, Pretty base, Pretty (TermN id)
         ,IsDPProblem base, MkProblem base (NTRS id)
         ,PprTPDBDot (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch


sc = apply DependencyGraphSCC >=> apply SubtermCriterion

graphTransform = apply NarrowingP .|. apply FInstantiation .|. apply Instantiation

--rpoPlusTransforms ::
rpoPlusTransforms rpo =  apply DependencyGraphSCC >=>
                         repeatSolver 3 (apply (RPOProc rpo Yices) .|. graphTransform >=>
                                         apply DependencyGraphSCC
                                        )

-- -------------------
-- Embedded content
-- -------------------

defaultForm = $(embedFile "resources/form.html")
defaultCss  = $(embedFile "style/narradar.css")