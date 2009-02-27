{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GADTs #-}

module Solver where

import Control.Applicative
import Control.Monad.Free
import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Data.Monoid
import Data.Traversable
import Text.XHtml (Html, primHtml)
import Data.Typeable
import Language.Prolog.TypeChecker as Prolog (TypeAssignment)

import ArgumentFiltering (typeHeu, innermost, AF_)
import Lattice
import qualified ArgumentFiltering as AF
import Proof
import PrologProblem
import NarrowingProblem
import GraphTransformation
import Aprove
import DPairs
import Types
import TRS
import ExtraVars
import UsableRules

import Prelude hiding (Monad(..))
import qualified Prelude

type Solver id f s m = ProblemG id f -> PPT id f s m
type Solver' id f id' f' s m = ProblemG id f -> PPT id' f' s m

defaultTimeout = 10

trivialProc p@(Problem typ trs dps@TRS{})
    | all (null.properSubterms.rhs) (TRS.rules dps) || any (\(l:->r) -> l == r) (TRS.rules dps)
    = failP Trivial p (primHtml "loop")
    | otherwise = returnM p
trivialProc  p = returnM p

aproveSrvP timeout = trivialProc >=> (wrap' . aproveSrvProc timeout)
aproveWebP = trivialProc >=> (wrap' . aproveWebProc)
aproveLocalP path = trivialProc >=> (wrap' . aproveProc path)

--webSolver, localSolver, srvSolver :: Solver Html IO BasicId
--narradarSolver :: Solver Html IO BasicId -> Solver Html IO BasicId

-- solver that connects to the Aprove web site, use only for testing
webSolver         = narradarSolver' aproveWebP

-- solver that uses a cmd line version of Aprove, use only for testing
localSolver       = localSolver' "/usr/local/lib/aprove/runme"
localSolver' path = narradarSolver' (aproveLocalP path)

-- solver that uses an Aprove server running on the host machine

pureSolver = narradarSolver' returnM

-- Our main solving scheme

{-# SPECIALIZE narradarSolver :: Problem BBasicId -> PPT Id BBasicId Html IO #-}
narradarSolver       = narradarSolver' (aproveSrvP defaultTimeout)
narradarSolver' aproveS p
   | isRewritingProblem    p = aproveS p
   | isAnyNarrowingProblem p = narrowingSolver 3 aproveS p

allSolver = allSolver' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
allSolver' heu k p
   | isRewritingProblem    p = k (convert p)
   | isPrologProblem       p = prologSolver' heu k p
   | isAnyNarrowingProblem p = narrowingSolver 3 k (convert p)

prologSolver_noL' :: (Bottom :<: f, Bottom :<: f', Hole :<: f', ConvertT f f', ConvertT Basic f, DPMark f id, DPMark f' (Labelled id), Monad m, MapLabelT f', Lattice (AF_ id), Lattice (AF_ (Labelled id))) =>
                     (forall sig .SignatureC sig id => Prolog.TypeAssignment -> sig -> AF.Heuristic id f)
                         -> Solver (Labelled id) f' Html m -> Solver' id f (Labelled id) f' Html m
prologSolver_noL    = prologSolver_noL' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver_noL' (heu :: (forall sig .SignatureC sig id => Prolog.TypeAssignment -> sig -> AF.Heuristic id f)) k = (prologP_sk heu >=> (return.convert) >=> narrowingSolverScc 1 k)

{-# SPECIALIZE prologSolver :: Problem BBasicId -> PPT LId BBasicLId Html IO #-}
prologSolver    = prologSolver' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver' heu k = -- (prologP_sk >=> (return.convert) >=> narrowingSolverScc 1 k) .|.
                      (prologP_labelling_sk heu >=> narrowingSolverScc 1 k)

prologSolver_one        = prologSolver_one' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver_one' heu k = (prologP_labelling_sk heu >=> usableSCCsProcessor >=> narrowingSolver 1 k)

{-# SPECIALIZE prologSolver_rhs :: Problem BBasicId -> PPT LId BBasicLId Html IO #-}
prologSolver_rhs = prologSolver_rhs' (aproveSrvP defaultTimeout)
prologSolver_rhs' k = (prologP_sk_rhs >=> (return.convert) >=> narrowingSolverScc 1 k) .|. prologP_labelling_sk_rhs >=> narrowingSolverScc 1 k

narrowingSolver 0 _ = const mzeroM
narrowingSolver 1 k = cycleProcessor >=> iUsableProcessor >=> groundRhsOneP >=> k
narrowingSolver depth _ | depth < 0 = error "narrowingSolver: depth must be positive"
narrowingSolver depth k =
       cycleProcessor >=> iUsableProcessor >=>
       ((groundRhsOneP >=> k)
        .|.
        (refineNarrowing >=> narrowingSolver (depth-1) k))

narrowingSolverScc 0 _ = const mzeroM
narrowingSolverScc 1 k = sccProcessor >=> iUsableProcessor >=> groundRhsAllP >=> k
narrowingSolverScc depth _ | depth < 0 = error "narrowingSolverScc: depth must be positive"
narrowingSolverScc depth k =
       usableSCCsProcessor >=> iUsableProcessor >=>
       ((groundRhsAllP >=> k)
        .|.
        (refineNarrowing >=> narrowingSolverScc (depth-1) k))

refineNarrowing = instantiation .|. finstantiation .|. narrowing

refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => Int -> (a -> m a) -> (a -> m' a) -> a -> m a
refineBy maxDepth f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

--runSolver :: (TRS Cf, Hole :<: f, Monoid out) => Solver id out IO f -> ProblemProofG id out f -> IO (ProblemProofG id out f)
runSolver solver p = runProofT (p >>= solver)

infixl 1 .|.
(.|.) :: MPlus m m m => (b -> m a) -> (b -> m a) -> b -> m a
f .|. g = \x -> f x `mplus` g x

