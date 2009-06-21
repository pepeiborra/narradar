{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Narradar.Processor.Graph where

import Control.Exception (assert)
import Data.Array as A
import Data.Graph as G
import Data.Tree  as Tree
import Data.Maybe
import Data.Strict.Tuple
import qualified Data.Set as Set
import Prelude hiding (pi)

import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework.Proof
import Narradar.Types
import Narradar.Utils


-- ----------------------------------------
-- Computing the estimated Dependency Graph
-- ----------------------------------------

getEDG p = filterSEDG p $ getdirectEDG p

getdirectEDG :: (Ord id, Ord v, Enum v) => Problem id v -> G.Graph
getdirectEDG p@(Problem _ _ (DPTRS dps _ (unif :!: _) _)) =
    assert (isValidUnif p) $
    G.buildG (A.bounds dps) [ xy | (xy, Just _) <- A.assocs unif]

filterSEDG :: (Ord id) => Problem id v -> G.Graph -> G.Graph
filterSEDG (Problem _ _ dptrs@DPTRS{}) gr =
    G.buildG (A.bounds gr)
               [ (i,j) | (i,j) <- G.edges gr
                       , isJust (dpUnifyInv dptrs j i)]

-- -------------------------------------
-- DP Processors transforming the graph
-- -------------------------------------
cycleProcessor, sccProcessor :: (Ppr v, Ord v, Enum v, Ppr id, Ord id) => Problem id v -> ProblemProofG id v
usableSCCsProcessor :: (Ppr v, Ord v, Enum v) => Problem LPId v -> ProblemProofG LPId v

usableSCCsProcessor problem@(Problem typ@GNarrowingModes{goal} trs dps@(DPTRS dd _ unif sig))
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

sccProcessor problem@(Problem typ trs dps@(DPTRS _ _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise =  andP (SCCGraph gr (map Set.fromList cc)) problem
                 [return $ mkProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where dd = rulesArray dps
          gr = getEDG problem
          cc = filter isCycle (map Tree.flatten (G.scc gr))
          isCycle [n] = n `elem` gr A.! n
          isCycle _   = True

cycleProcessor problem@(Problem typ trs (DPTRS dd _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ mkProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where cc = cycles gr
          gr = getEDG problem
