{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GADTs #-}

module Narradar.Solver where

import Control.Applicative
import Control.Monad.Free
import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Data.Monoid
import Data.Traversable
import Text.XHtml (Html, primHtml)
import Data.Typeable
import TRS
import TRS.FetchRules
import TRS.FetchRules.TRS
import Lattice

import Narradar.ArgumentFiltering (typeHeu, innermost, AF_)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Aprove
import Narradar.DPairs
import Narradar.Proof
import Narradar.Types
import Narradar.NarrowingProblem
import Narradar.PrologProblem
import Narradar.GraphTransformation
import Narradar.UsableRules

import qualified Prelude
import Prelude hiding (Monad(..))

type Solver id f s m = ProblemG id f -> PPT id f s m
type Solver' id f id' f' s m = ProblemG id f -> PPT id' f' s m

defaultTimeout = 10

-- --------------
-- Aprove flavors
-- --------------
aproveSrvP timeout = trivialNonTerm >=> (wrap' . aproveSrvProc2 Default timeout)
aproveWebP         = trivialNonTerm >=> (wrap' . aproveWebProc)
aproveLocalP path  = trivialNonTerm >=> (wrap' . aproveProc path)

-- ------------------------
-- Trivial nonTermination
-- ------------------------

trivialNonTerm p@(Problem typ trs dps@TRS{})
    | all (null.properSubterms.rhs) (TRS.rules dps) || any (\(l:->r) -> l == r) (TRS.rules dps)
    = failP Trivial p (primHtml "loop")
    | otherwise = returnM p
trivialNonTerm  p = returnM p

-- ----------------------
-- Processor-like Parsers
-- ----------------------
-- TODO Allow for goals in Narrowing problems
parseTRS :: ProblemType Id -> String -> PPT Id BasicId Html IO
parseTRS typ txt = wrap' $ go$ do
                      rules :: [Rule Basic] <- eitherIO$ parseFile trsParser "" txt
                      let trs = mkTRS rules :: NarradarTRS String Basic'
                      return (mkGoalProblem AF.bestHeu AllTerms $ mkDPProblem Narrowing trs)

parseProlog :: String -> PPT String Basic' Html IO
parseProlog = wrap' . Prelude.return . either error Prelude.return . parsePrologProblem

-- ------------------
-- Some Basic solvers
-- ------------------
prologSolver    = prologSolver' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver' heu k = (prologP_labelling_sk heu >=> narrowingSolverUScc >=> k)
  where narrowingSolverUScc = usableSCCsProcessor >=> iUsableProcessor >=> groundRhsAllP

-- narradar 1.0 main solving scheme
narradarSolver       = narradarSolver' aproveWebP
narradarSolver' aproveS = cycleProcessor >=> groundRhsOneP >=> aproveS

narrowingSolver 0 _ = const mzeroM
narrowingSolver 1 k = cycleProcessor >=> iUsableProcessor >=> groundRhsOneP >=> k
narrowingSolver depth _ | depth < 0 = error "narrowingSolver: depth must be positive"
narrowingSolver depth k =
       cycleProcessor >=> iUsableProcessor >=>
       ((groundRhsOneP >=> k)
        .|.
        (refineNarrowing >=> narrowingSolver (depth-1) k))
  where refineNarrowing = instantiation .|. finstantiation .|. narrowing

-- -------------
-- Combinators
-- -------------
refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => Int -> (a -> m a) -> (a -> m' a) -> a -> m a
refineBy maxDepth f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

--runSolver :: (TRS Cf, Hole :<: f, Monoid out) => Solver id out IO f -> ProblemProofG id out f -> IO (ProblemProofG id out f)
--runSolver solver p = runProofT (p >>= solver)

infixl 1 .|.
(.|.) :: MPlus m m m => (b -> m a) -> (b -> m a) -> b -> m a
f .|. g = \x -> f x `mplus` g x

eitherIO = either (error.show) return