{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
module Solver where

import Control.Applicative
import Control.Monad.Free
import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Text.XHtml (Html)

import Problem
import NarrowingProblem
import GraphTransformation
import Aprove
import DPairs
import Types
import TRS.Utils

import Prelude hiding (Monad(..))
import qualified Prelude

infixl 1 .|.

type Solver s m f =  (Ord (Term f), IsVar f, Hole :<: f, AnnotateWithPos f f, Types.Ppr f, Monad m) => Problem f -> PPT s m f

webSolver, localSolver, srvSolver :: Solver Html IO f
mainSolver :: Solver Html IO f -> Solver Html IO f
--mainSolverBase :: Ord (Term f) => ((Problem f -> ProblemProgress s f) -> solver) -> solver

-- solver that connects to the Aprove web site, use only for testing
webSolver      = mainSolver (wrap' . aproveWebProc)

-- solver that uses a cmd line version of Aprove, use only for testing
localSolver       = localSolver' "/usr/local/lib/aprove/runme"
localSolver' path = mainSolver (wrap' . aproveProc path)

-- solver that uses an Aprove server running on the host machine
srvSolver = mainSolver (wrap' . aproveSrvProc)
srvSolverSerial = mainSolverSerial (wrap' . aproveSrvProc)

-- Attempts to connect to the Aprove local server, falls back to the Aprove web server
--srvWebSolver = 

-- Our main solving scheme
mainSolverBase k = cycleProcessor >=>
                   (k afProcessor) -- `refineBy` (narrowingProcessor >=> cycleProcessor))


mainSolver aproveProc = mainSolverBase (>||> aproveProc)
mainSolverSerial aproveProc = mainSolverBase (>=> aproveProc)

-- For debugging purposes
mainSolverPure = mainSolverBase id


maxDepth = 2
refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => (a -> m a) -> (a -> m' a) -> a -> m a
refineBy f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

runSolver :: (IsVar f, Ord(Term f), Hole :<: f, AnnotateWithPos f f, Types.Ppr f, Monad m) => Solver Html m f -> TRS Identifier f -> m (ProblemProgress Html f)
runSolver solver trs@TRS{} = runProgressT (startSolver trs >>= solver)

startSolver :: TRS Identifier f -> ProblemProgress Html f
startSolver trs@TRS{} = returnM (mkNDPProblem trs)

(.|.) :: MPlus m m m => (b -> m a) -> (b -> m a) -> b -> m a
f .|. g = \x -> f x `mplus` g x