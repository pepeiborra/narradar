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
import Data.Monoid
import Data.Traversable
import Text.XHtml (Html, primHtml)

import Proof
import PrologProblem
import NarrowingProblem
import GraphTransformation
import Aprove
import DPairs
import Types
import TRS

import Prelude hiding (Monad(..))
import qualified Prelude

type Solver id s m f = ProblemG id f -> PPT id s m f

trivialProc p@(Problem typ trs dps@TRS{})
    | all (null.properSubterms.rhs) (TRS.rules dps) || any (\(l:->r) -> l == r) (TRS.rules dps)
    = failP Trivial p (primHtml "loop")
    | otherwise = returnM p
trivialProc  p = returnM p

--webSolver, localSolver, srvSolver :: Solver Html IO BasicId
--narradarSolver :: Solver Html IO BasicId -> Solver Html IO BasicId

-- solver that connects to the Aprove web site, use only for testing
webSolver         = narradarSolver' (wrap' . aproveWebProc)

-- solver that uses a cmd line version of Aprove, use only for testing
localSolver       = localSolver' "/usr/local/lib/aprove/runme"
localSolver' path = narradarSolver' (wrap' . aproveProc path)

-- solver that uses an Aprove server running on the host machine

pureSolver = narradarSolver' returnM

-- Our main solving scheme

{-# SPECIALIZE narradarSolver :: Problem BBasicId -> PPT Id Html IO BBasicId #-}
narradarSolver       = narradarSolver' (trivialProc >=> (wrap' . aproveSrvProc))
narradarSolver' aprove p
   | isRewritingProblem    p = aprove p
--   | isPrologProblem       p = prologSolver aprove p
   | isAnyNarrowingProblem p = narrowingSolver aprove p

allSolver = allSolver' (trivialProc >=> (wrap' . aproveSrvProc)) (trivialProc >=> (wrap' . aproveWebProc))
allSolver' aproveS aproveL p
   | isRewritingProblem    p = aproveS (convert p)
   | isPrologProblem       p = prologSolver'   aproveS aproveL p
   | isAnyNarrowingProblem p = narrowingSolver aproveS (convert p)

{-# SPECIALIZE prologSolver :: Problem BBasicId -> PPT LId Html IO BBasicLId #-}
prologSolver = prologSolver' (trivialProc >=> (wrap' . aproveSrvProc)) (trivialProc >=> (wrap' . aproveWebProc))
prologSolver' aproveShort aproveLong =
      (prologP_sk >=> (return.convert) >=> graphProcessor >=> afProcessor >=> aproveShort)
  .|. (prologP_labelling_sk            >=> graphProcessor >=> afProcessor >=> aproveLong)

narrowingSolver aprove =
       graphProcessor >=> afProcessor >=> aprove
                           `refineBy`
       (instantiation .|. finstantiation .|. narrowing)

maxDepth = 1
refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => (a -> m a) -> (a -> m' a) -> a -> m a
refineBy f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

--runSolver :: (TRS Cf, Hole :<: f, Monoid out) => Solver id out IO f -> ProblemProofG id out f -> IO (ProblemProofG id out f)
runSolver solver p = runProofT (p >>= solver)

infixl 1 .|.
(.|.) :: MPlus m m m => (b -> m a) -> (b -> m a) -> b -> m a
f .|. g = \x -> f x `mplus` g x

