{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GADTs #-}

module Narradar.Solver where

import Control.Applicative hiding (Alternative(..))
import Control.Arrow hiding (first)
import qualified Control.Monad as P
import Control.Monad.Free
import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Data.Foldable (toList)
import Data.Monoid
import Data.Traversable
import Language.Prolog.TypeChecker
import Text.ParserCombinators.Parsec (ParseError)
import Text.XHtml (Html, primHtml)
import TRS
import TRS.FetchRules
import TRS.FetchRules.TRS
import Lattice

import Narradar.ArgumentFiltering (typeHeu, typeHeu2, innermost, bestHeu, AF_)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Aprove
import Narradar.DPairs
import Narradar.Proof
import Narradar.Types
import Narradar.NarrowingProblem
import Narradar.PrologProblem
import Narradar.RewritingProblem
import Narradar.ReductionPair
import Narradar.GraphTransformation
import Narradar.UsableRules
import Narradar.Utils

import qualified Prelude
import Prelude hiding (Monad(..))

type Solver id f s m = ProblemG id f -> PPT id f s m
type Solver' id f id' f' s m = ProblemG id f -> PPT id' f' s m

defaultTimeout = 10

-- --------------
-- Aprove flavors
-- --------------
aproveSrvP timeout = trivialP >=> (wrap' . aproveSrvProc2 Default timeout)
aproveWebP         = trivialP >=> (wrap' . aproveWebProc)
aproveLocalP path  = trivialP >=> (wrap' . aproveProc path)


-- ----------------------
-- Processor-like Parsers
-- ----------------------
-- TODO Allow for goals in Narrowing problems
parseTRS :: ProblemType Id -> String -> PPT Id BasicId Html (Either ParseError)
parseTRS typ txt = wrap' $ do
                      rules :: [Rule Basic] <- parseFile trsParser "" txt
                      let trs = mkTRS rules :: NarradarTRS String Basic'
                      P.return $ msum (map returnM $ mkGoalProblem AF.bestHeu Narrowing trs)

--parseProlog :: String -> PPT String Basic' Html IO
parseProlog = eitherM . fmap (inferType &&& id) . parsePrologProblem

-- ------------------
-- Some Basic solvers
-- ------------------

prologSolver  typ   = prologSolver' (typeHeu2 typ) (typeHeu typ)
prologSolver' h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolver h2
  where
   narrowingSolver heu = solveB 3 ((trivialP >=> reductionPair heu 20 >=> sccProcessor) <|>
                                   refineNarrowing)

refineNarrowing = instantiation <|> finstantiation <|> narrowing
refineNarrowing' = reducingP (narrowing >=> sccProcessor) <|>
                   reducingP (finstantiation >=> sccProcessor) <|>
                   reducingP (instantiation >=> sccProcessor)

-- narradar 1.0 main solving scheme
narradarSolver          = narradarSolver' aproveWebP
narradarSolver' aproveS = cycleProcessor >=> groundRhsOneP bestHeu >=> aproveS

narrowingSolver 0 _ = const mzeroM
narrowingSolver 1 k = cycleProcessor >=> iUsableRulesP >=> groundRhsOneP bestHeu >=> k
narrowingSolver depth _ | depth < 0 = error "narrowingSolver: depth must be positive"
narrowingSolver depth k =
       cycleProcessor >=> iUsableRulesP >=>
       ((groundRhsOneP bestHeu >=> k)
        <|>
        (refineNarrowing >=> narrowingSolver (depth-1) k))

-- -------------
-- Combinators
-- -------------
-- Does not produce 'good-looking' proofs (the effect is only seen in failed searches)
solve' :: P.MonadPlus m => (a -> m a) -> a -> m a
solve' f x = let x' = f x in x' `P.mplus` (x' P.>>= solve' f)

{-
DANGEROUS. solve and solveB become unsound if used with alternatives
These combinators look at intermediate states of the proof (they use runProofT)
This does not play well with some optimizations inside runProofT
which cut nonproductive failure branches.
-}
solve f x = do
  fx <- lift $ runProofT (f x)
  if null(toList fx) then wrap fx else solve f P.=<< wrap fx

solveB 0 f x = f x
solveB b f x = do
  fx <- lift $ runProofT (f x)
  if null(toList fx) then wrap fx else solveB (b-1) f P.=<< wrap fx

refineBy :: (Prelude.Monad m, Bind m' m m, MPlus m m m) => Int -> (a -> m a) -> (a -> m' a) -> a -> m a
refineBy maxDepth f refiner = loop maxDepth where
  loop 0 x = f x
  loop i x = f x `mplus` (refiner x >>= loop (i-1))

firstP :: [a -> Proof s a] -> a -> Proof s a
firstP [] _ = P.mzero
firstP (a:alternatives) p = case a p of
                             Impure MZero      -> firstP alternatives p
                             Impure DontKnow{} -> firstP alternatives p
                             anything_else     -> anything_else
{-
first :: P.Monad m => [a -> ProofT s m a] -> a -> ProofT s m a
first [] _ = mzeroM
first (a:alternatives) p = FreeT $ do
                           x <- unFreeT (a p)
                           case x of
                             Right MZero          -> unFreeT(first alternatives p)
                             p@(Right DontKnow{}) -> unFreeT(first alternatives p)
                             anything_else        -> P.return anything_else
-}
-- reducingP :: (a -> ProblemProofG id s f) -> a -> ProblemProofG id s f
reducingP solver p = solver p >>= \p' -> guard (length (rules p') <= length (rules p)) >> return p'

--runSolver :: (TRS Cf, Hole :<: f, Monoid out) => Solver id out IO f -> ProblemProofG id out f -> IO (ProblemProofG id out f)
--runSolver solver p = runProofT (p >>= solver)
infixl 3 <|>
(<|>) = liftM2 mplus