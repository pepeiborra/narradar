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
import Text.XHtml (Html)

import Proof
import PrologProblem
import NarrowingProblem
import GraphTransformation
import Aprove
import DPairs
import Types
import TRS.Utils

import Prelude hiding (Monad(..))
import qualified Prelude

type Solver s m f = (Ord (Term f), IsVar f, Hole :<: f, Zip f, AnnotateWithPos f f, Types.Ppr f, Monad m) => Problem f -> PPT s m f

webSolver, localSolver, srvSolver :: Solver Html IO BasicId
narradarSolver :: Solver Html IO BasicId -> Solver Html IO BasicId

-- solver that connects to the Aprove web site, use only for testing
webSolver         = narradarSolver (wrap' . aproveWebProc)

-- solver that uses a cmd line version of Aprove, use only for testing
localSolver       = localSolver' "/usr/local/lib/aprove/runme"
localSolver' path = narradarSolver (wrap' . aproveProc path)

-- solver that uses an Aprove server running on the host machine
srvSolver       = narradarSolver (wrap' . aproveSrvProc)

pureSolver = narradarSolver returnM

-- Our main solving scheme
narradarSolver aprove p
   | isRewritingProblem    p = aprove p
   | isPrologProblem       p = prologSolver aprove p
   | isAnyNarrowingProblem p = narrowingSolver aprove p

prologSolver aprove    = (prologP_sk) >=> graphProcessor >=> afProcessor >=> aprove
narrowingSolver aprove =
       graphProcessor >=> afProcessor >=> aprove
                           `refineBy`
       (instantiation .|. finstantiation .|. narrowing)

maxDepth = 1
refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => (a -> m a) -> (a -> m' a) -> a -> m a
refineBy f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

runSolver :: (Traversable f, Ord (Term f), IsVar f, Hole :<: f, Zip f, AnnotateWithPos f f, Types.Ppr f, Monoid out) =>
             Solver out IO f -> ProblemProof out f -> IO (ProblemProof out f)
runSolver solver p = runProofT (p >>= solver)
{-
startSolver :: TRS Identifier f -> ProblemProof Html f
startSolver trs@TRS{} = returnM (mkNDPProblem Nothing trs)
startSolver' :: Maybe Goal -> TRS Identifier f -> ProblemProof Html f
startSolver' mb_goal trs@TRS{} = returnM (mkNDPProblem mb_goal trs)
-}
infixl 1 .|.
(.|.) :: MPlus m m m => (b -> m a) -> (b -> m a) -> b -> m a
f .|. g = \x -> f x `mplus` g x

