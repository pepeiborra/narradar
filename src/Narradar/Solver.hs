{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Narradar.Solver where

import Control.Arrow hiding (first)
import Control.Monad.Free
import Control.Monad.Free.Improve
import Control.Monad.Logic
import Data.Maybe (fromMaybe)
import System.IO.Unsafe

import Narradar.Types.ArgumentFiltering (typeHeu, typeHeu2, bestHeu)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Processor.Aprove
import Narradar.Framework.Proof
import Narradar.Types
import Narradar.Processor.Graph
import Narradar.Processor.NarrowingProblem
import Narradar.Processor.PrologProblem
import Narradar.Processor.RewritingProblem
import Narradar.Processor.ReductionPair
import Narradar.Processor.GraphTransformation
import Narradar.Processor.UsableRules
import Narradar.Utils


import qualified Prelude
import Prelude hiding (Monad(..))

type Solver id f m = Problem id f -> PPT id f m
type Solver' id f id' f' m = Problem id f -> PPT id' f' m

defaultTimeout = 15

-- --------------
-- Aprove flavors
-- --------------
aproveSrvP timeout = trivialP >=> (unsafePerformIO . aproveSrvProc2 Default timeout)
aproveWebP         = trivialP >=> (unsafePerformIO . aproveWebProc)
aproveLocalP path  = trivialP >=> (unsafePerformIO . aproveProc path)


-- ----------------------
-- Processor-like Parsers
-- ----------------------
parseProlog :: (Monad m) => String -> m (SharingAssignment String, Problem String Var)
parseProlog = eitherM . fmap (inferType &&& id) . toEither . parsePrologProblem

-- ------------------
-- Some Basic solvers
-- ------------------
prologSolver opts typ = prologSolver' opts (typeHeu2 typ) (typeHeu typ)
prologSolver' _opts h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolver
  where narrowingSolver = refineBy 4 (solve' (msum . uGroundRhsAllP h2 >=> aproveWebP))
                                     refineNarrowing

prologSolverOne' _opts h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolver
  where narrowingSolver = refineBy 4 (solve' (msum . reductionPair h2 20 >=> sccProcessor))
                                     refineNarrowing

pSolver :: Monad m => options -> (prob -> C (Free ProofF) a) -> prob -> m (Bool, ProofC a, String)
pSolver _ solver p = return (maybe False (const True) sol, fromMaybe iprob sol, "") where
    prob  = solver p
    iprob = improve prob
    sol   = runProof' iprob `asTypeOf` Just iprob

refineNarrowing = firstP [ msumPar . instantiation
                         , msumPar . finstantiation
                         , msumPar . narrowing ] >=> sccProcessor

refineNarrowing' = reducingP ((msum.narrowing) >=> sccProcessor) <|>
                   reducingP ((msum.finstantiation) >=> sccProcessor) <|>
                   reducingP ((msum.instantiation) >=> sccProcessor)

-- narradar 1.0 main solving scheme
narradarSolver          = narradarSolver' aproveWebP
narradarSolver' aproveS = cycleProcessor >=> msum . groundRhsOneP bestHeu >=> aproveS

narrowingSolver 0 _ = const mzero
narrowingSolver 1 k = cycleProcessor >=> usableRulesP >=> msum . groundRhsOneP bestHeu >=> k
narrowingSolver depth _ | depth < 0 = error "narrowingSolver: depth must be positive"
narrowingSolver depth k =
       cycleProcessor >=> usableRulesP >=>
       ((msum . groundRhsOneP bestHeu >=> k)
        <|>
        (refineNarrowing >=> narrowingSolver (depth-1) k))
-- -------------
-- Combinators
-- -------------

{-
DANGEROUS. solve and solveB become unsound if used with alternatives
These combinators look at intermediate states of the proof (they use runProofT)
This does not play well with some optimizations inside runProofT
which cut nonproductive failure branches.
-}
{-
solveT f x = do
  fx <- lift $ runProofT (f x)
  if null(toList fx) then wrap fx else solveT f =<< wrap fx

solveBT 0 f x = f x
solveBT b f x = do
  fx <- lift $ runProofT (f x)
  if isSuccess fx then wrap fx else solveBT (b-1) f =<< wrap fx
-}

solve' :: MonadPlus m => (a -> m a) -> a -> m a
-- Does not produce 'good-looking' proofs
solve' f x = let x' = f x in x' `mplus` (x' >>= solve' f)

solve f x = let fx = f x in if isSuccess fx then fx else (fx >>= solve f)

solveB 0 f x = f x
solveB b f x = let fx = f x in if isSuccess fx then fx else solveB (b-1) f =<< fx

--refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => Int -> (a -> m a) -> (a -> m' a) -> a -> m a
refineBy maxDepth f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

--firstP :: [a -> Proof s a] -> a -> Proof s a
firstP [] _ = mzero
firstP (a:alternatives) p = do
  ei_free <- free (a p)
  case ei_free of
    Right MZero -> firstP alternatives p
    Right x     -> wrap x
    Left  z     -> return z

first :: Monad m => [a -> ProofT m a] -> a -> ProofT m a
first [] _ = mzero
first (a:alternatives) p = FreeT $ do
                           x <- unFreeT (a p)
                           case x of
                             Right MZero      -> unFreeT(first alternatives p)
                             Right DontKnow{} -> unFreeT(first alternatives p)
                             anything_else    -> return anything_else


--reducingP ::  (MonadPlus m, TRS t id f, Return m) => (t -> m t) -> t -> m t
reducingP solver p =  do
  p' <- solver p
  guard (length (rules p') <=length (rules p))
  return p'

--runSolver :: (TRS Cf, Hole :<: f, Monoid out) => Solver id out IO f -> ProblemProofG id out f -> IO (ProblemProofG id out f)
--runSolver solver p = runProofT (p >>= solver)
infixl 3 <|>
(<|>) = liftM2 mplus
msumF  = foldr (<|>) (const mzero)
msumParF = foldr (liftM2 mplusPar) (const mzero)
