
{-# LANGUAGE ScopedTypeVariables, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Narradar.DPairs where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad (liftM)
import Data.Array.Base (numElements)
import qualified Data.Array.IArray as A
import qualified Data.Graph as G
import Data.Char
import Data.List ((\\), partition)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable as T
import qualified Data.Tree as Tree
import Text.XHtml (toHtml, Html)
import Prelude as P hiding (pi)
import qualified TRSParser as TRS
import qualified TRSTypes  as TRS
import TRSTypes hiding (Id, Term, Narrowing, SimpleRuleF(..))
import Text.ParserCombinators.Parsec (runParser)

import Narradar.ArgumentFiltering (AF_,AF, LabelledAF, Heuristic(..), PolyHeuristicN, bestHeu, typeHeu, MkHeu, mkHeu)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Types hiding (Other)
import Narradar.Utils
import Narradar.Proof
import Narradar.ExtraVars
import Narradar.UsableRules
import Narradar.Term
import Narradar.Var
import Lattice
-- -----------------
-- Parsing TPDB TRSs
-- -----------------
-- Here to avoid introducing recursive module dependencies

parseTRS :: Monad m => String -> m (ProblemG Id Var)
parseTRS = eitherM . runParser trsParser mempty "<input>"

trsParser :: TRS.TRSParser (ProblemG Id Var)
trsParser = do
  Spec spec <- TRS.trsParser
  let r = mkTRS $ concat [mkRules rr | Rules rr <- spec]
      p = concat [mkDPs   rr | Pairs rr <- spec]
      mkStrat                                              :: Monad m => TRS.Strategy -> m (ProblemType Id)
      mkStrat InnerMost                                    = return InnermostRewriting
      mkStrat OuterMost                                    = return Rewriting
      mkStrat TRS.Narrowing                                = return Narrowing
      mkStrat ConstructorNarrowing                         = return GNarrowing
      mkStrat BasicNarrowing                               = return BNarrowing
      mkStrat (TRS.NarrowingG            (TRS.Term id tt)) = return (narrowingModes  r (id,tt))
      mkStrat (TRS.BasicNarrowingG       (TRS.Term id tt)) = return (bNarrowingModes r (id,tt))
      mkStrat (TRS.ConstructorNarrowingG (TRS.Term id tt)) = return (gNarrowingModes r (id,tt))
      mkStrat s                                            = fail ("Unknown strategy: " ++ show s)

  strategy <- maybe (return Rewriting) mkStrat $ listToMaybe [s | Strategy s <- spec]
  return $ case p of
     [] -> mkDPProblem strategy r
     _  -> mkProblem strategy (convert r) (dpTRS (convert strategy) (convert r) p emptyArray)
          -- TODO Consider goal problems when the PAIRS set is not empty
 where
  mkDPs   rr = map markDPRule (convert $ mkRules rr)
  mkRules rr = [ toTerm l :-> toTerm r | Rule (l TRS.:-> r) _ <- rr] where
           toTerm = foldTerm toVar (Impure . fromSimple)
           allvars = Map.fromList (Set.toList(getVars rr) `zip` [0..])
           toVar v = var' (Just v) (fromJust $ Map.lookup v allvars)


-- -------------------------
-- Constructing DP problems
-- -------------------------

-- THERE IS A SERIOUS BUG IN GHC 6.10.1 WITH INSTANCE RESOLUTION IN PRESENCE OF TYPE FUNCTIONS AND OVERLOADING
-- IT IS NO LONGER TRUE THAT THE MOST SPECIFIC INSTANCE IS PICKED, SINCE TYPE EXPRESSIONS ARE NOT REDUCED
-- SO STAY AWAY FROM TYPE FUNCTIONS FOR NOW !!!!!!!!!!!!

-- | Constructing DP problems. Do not construct a goal problem with this function, for that use 'mkGoalProblem'
mkDPProblem :: (Ppr id, Ord a, id ~ Identifier a) => ProblemType id -> NarradarTRS a Var -> ProblemG id Var
mkDPProblem typ _ | isModed typ = error "To create a goal problem use 'mkGoalProblem'"
mkDPProblem typ trs = mkProblem typ trs' (mkDPs typ trs') where trs' = convert trs

-- | Construct the set of pairs corresponding to a problem type and a TRS R of rules.
mkDPs :: (Ord a, id ~ Identifier a) => ProblemType id -> NarradarTRS id Var -> NarradarTRS id Var
mkDPs typ trs
    | isFullNarrowing typ = dpTRS typ trs (getNPairs trs) emptyArray
    | otherwise           = dpTRS typ trs (getPairs  trs) emptyArray

-- | Constructing NDP problems with as starting goal. This function takes an AF heuristic.
--   This is necessary so early because before splitting P into SCCs we need to ensure
--   that P is indeed a TRS (no extra variables).
--   I.e. we need to compute the filtering 'globally'
mkGoalProblem :: (Ppr id, Ord a, PolyHeuristicN heu id, Lattice (AF_ id), id ~ Identifier a) =>
                 MkHeu heu -> ProblemType a -> NarradarTRS a Var -> [ProblemG id Var]
mkGoalProblem heu typ trs =
    let trs'       = convert trs
        dps        = mkDPs typ' trs'
        typ'       = typ{pi=extendedPi, goal=AF.extendToTupleSymbols (goal typ)}
        extendedPi = AF.extendToTupleSymbols (pi typ)
        p0         = mkProblem typ' trs' dps
        orProblems = case mkHeu heu p0 of
                       heu -> [assert (isSoundAF pi' p0) $
                               mkProblem typ'{pi=pi'} trs' dps
                                   | pi' <- Set.toList $ invariantEV heu (rules p0) extendedPi]
    in assert (not $ null orProblems) orProblems

-- -------------------------------------
-- DP Processors transforming the graph
-- -------------------------------------
cycleProcessor, sccProcessor :: (Ppr v, Ord v, Ppr id, Ord id) => ProblemG id v -> ProblemProofG id v
usableSCCsProcessor :: (Ppr v, Ord v) => ProblemG LPId v -> ProblemProofG LPId v

usableSCCsProcessor problem@(Problem typ@GNarrowingModes{pi,goal} trs dps@(DPTRS dd _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise =  andP (UsableGraph gr reachable) problem
                 [return $ mkProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo)
                      | ciclo <- cc, any (`Set.member` reachable) ciclo]
  where
   gr          = getEDG problem
   cc          = filter isCycle (map Tree.flatten (G.scc gr)) --TODO Use the faster GraphSCC package
   reachable   = Set.fromList (G.reachable gr =<< goal_pairs)
   goal_pairs  = [ i | (i,r) <- [0..] `zip` rules dps, Just f <- [rootSymbol (lhs r)], unmarkDPSymbol f `Set.member` AF.domain goal]
   isCycle [n] = n `elem` gr A.! n
   isCycle _   = True


usableSCCsProcessor p = sccProcessor p

sccProcessor problem@(Problem typ trs dps@(DPTRS dd _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise =  andP (SCCGraph gr (map Set.fromList cc)) problem
                 [return $ mkProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where dd = rulesArray dps
          gr = getEDG problem
          cc = filter isCycle (map Tree.flatten (G.scc gr))
          isCycle [n] = n `elem` gr A.! n
          isCycle _   = True

cycleProcessor problem@(Problem typ trs dps@(DPTRS dd _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ mkProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where cc = cycles gr
          gr = getEDG problem

-- ----------------------------------------
-- Computing the estimated Dependency Graph
-- ----------------------------------------

getEDG p = getdirectEDG p

getdirectEDG :: (Ord id) => ProblemG id v -> G.Graph
getdirectEDG p@(Problem typ trs dptrs@(DPTRS dps _ (unif :!: _) _)) =
    G.buildG (A.bounds dps) [ xy | (xy, Just _) <- A.assocs unif]

filterSEDG :: (Ord id) => ProblemG id v -> G.Graph -> G.Graph
filterSEDG (Problem typ trs dptrs@DPTRS{}) gr =
    G.buildG (A.bounds gr)
               [ (i,j) | (i,j) <- G.edges gr
                       , isJust (dpUnifyInv dptrs j i)]

-- ---------------------------
-- Computing Dependency Pairs
-- ---------------------------
--getPairs :: (Ord id, Ord v) => NarradarTRS id v -> [DP (TermF (Identifier id)) v]
getPairs trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isDefined trs) r]

--getNPairs :: (Ord id, Ord v) => NarradarTRS id v -> [DP (TermF (Identifier id)) v]
getNPairs trs = getPairs trs ++ getLPairs trs

--getLPairs :: (Ord id, Ord v) => NarradarTRS id v -> [DP (TermF (Identifier id)) v]
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined trs lp]


-------------------------
emptyArray = A.listArray (0,-1) []
