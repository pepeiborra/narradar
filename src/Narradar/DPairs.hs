
{-# LANGUAGE ScopedTypeVariables, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Narradar.DPairs where

import Control.Applicative
import Control.Exception (assert)
import Data.Array.Base (numElements)
import qualified Data.Array.IArray as A
import qualified Data.Graph as G
import Data.List ((\\))
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable as T
import qualified Data.Tree as Tree
import Text.XHtml (toHtml, Html)
import Prelude as P hiding (pi)

import qualified Narradar.ArgumentFiltering as AF
import Narradar.Types
import Narradar.Utils
import Narradar.Proof
import Narradar.ExtraVars
import Narradar.UsableRules

-- THERE IS A SERIOUS BUG IN GHC 6.10.1 WITH INSTANCE RESOLUTION IN PRESENCE OF TYPE FUNCTIONS AND OVERLOADING
-- IT IS NO LONGER TRUE THAT THE MOST SPECIFIC INSTANCE IS PICKED, SINCE TYPE EXPRESSIONS ARE NOT REDUCED
-- SO STAY AWAY FROM TYPE FUNCTIONS FOR NOW !!!!!!!!!!!!

--mkDPProblem :: (DPMark (DPVersionOf f), TRSC f, T id :<: f, T (Identifier id) :<: DPVersionOf f, Convert (Term f) (Term (DPVersionOf f)), TRSC (DPVersionOf f), Show (Identifier id), Ord id) => ProblemType id -> NarradarTRS id f -> ProblemG (Identifier id) (DPVersionOf f)
mkDPProblem :: (DPMark (DPVersionOf f), TRSC f, T id :<: f, T (Identifier id) :<: f', Convert (Term f) (Term f'), TRSC f', Show (Identifier id), Ord id, DPMark f') => ProblemType id -> NarradarTRS id f -> ProblemG (Identifier id) f'
mkDPProblem Narrowing trs = let trs' = convert trs in mkProblem Narrowing trs' (dpTRS Narrowing trs' (getNPairs trs') emptyArray)
--mkDPProblem BNarrowing trs = let trs' = convert trs in mkProblem BNarrowing trs' (dpTRS BNarrowing trs' (getPairs  trs') emptyArray)
mkDPProblem typ       trs = let trs' = convert trs; typ' = convert typ in mkProblem typ' trs' (dpTRS typ' trs' (getPairs  trs') emptyArray)

emptyArray = A.listArray (0,-1) []

getPairs :: (Ord id, T id :<: f, DPMark f) => NarradarTRS id f -> [DP f]
getPairs trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isDefined trs) r]

getNPairs :: (Ord id, T id :<: f, DPMark f) => NarradarTRS id f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: (Ord id, T id :<: f, DPMark f) => NarradarTRS id f -> [DP f]
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined trs lp]


{-# SPECIALIZE cycleProcessor :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE sccProcessor   :: Problem BBasicId -> ProblemProof Html BBasicId #-}
cycleProcessor, sccProcessor :: (T id :<: f, DPMark f, Show id, Ord id) => ProblemG id f -> ProblemProofG id Html f
usableSCCsProcessor :: forall f id. (T LPId :<: f, DPMark f) => ProblemG LPId f -> ProblemProofG LPId Html f

usableSCCsProcessor problem@(Problem typ@GNarrowingModes{pi,goal} trs dps@(DPTRS dd _ unif sig))
  | assert (isSoundAF pi problem) False = undefined
  | null cc   = success (UsableGraph gr reachable) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (UsableGraph gr reachable) problem
                 [return $ Problem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo)
                      | ciclo <- cc, any (`Set.member` reachable) ciclo]
  where
   gr          = getEDG problem
   cc          = filter isCycle (map Tree.flatten (G.scc gr))
   reachable   = Set.fromList (G.reachable gr =<< goal_pairs)
   goal_pairs  = [ i | (i,r) <- [0..] `zip` rules dps, Just f <- [rootSymbol (lhs r)], unmarkDPSymbol f `Set.member` AF.domain goal]
   isCycle [n] = n `elem` gr A.! n
   isCycle _   = True


usableSCCsProcessor p = sccProcessor p

sccProcessor problem@(Problem typ trs dps@(DPTRS dd _ unif sig))
  | null cc   = success (SCCGraph gr []) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (SCCGraph gr (map Set.fromList cc)) problem
                 [return $ Problem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where dd = rulesArray dps
          gr = getEDG problem
          cc = filter isCycle (map Tree.flatten (G.scc gr))
          isCycle [n] = n `elem` gr A.! n
          isCycle _   = True

cycleProcessor problem@(Problem typ trs dps@(DPTRS dd _ unif sig))
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where cc = cycles gr
          gr = getEDG problem

getEDG p = filterSEDG p $ getdirectEDG p

getdirectEDG :: (Ord id, T id :<: f, DPMark f) => ProblemG id f -> G.Graph
getdirectEDG p@(Problem typ trs dptrs@(DPTRS dps _ (unif :!: _) _)) | (isBNarrowing .|. isGNarrowing) typ =
    G.buildG (A.bounds dps) [ xy | (xy, Just _) <- A.assocs unif]

filterSEDG :: (Ord id, T id :<: f, DPMark f {-, HasTrie (f(Term f))-}) => ProblemG id f -> G.Graph -> G.Graph
filterSEDG (Problem typ trs (rulesArray->dps)) gr =
    G.buildG (0, length (G.vertices gr) - 1)
               [ (i,j) | (i,j) <- G.edges gr
                       , let _:->t = dps A.! i
                       , let u:->_ = dps A.! j
                       , inChain t u]
    where inChain t@(In in_t) u = unifies' u (ren $ hIn (icap (trs' t) <$> in_t))
          trs'
             | isBNarrowing typ || isGNarrowing typ = \t -> tRS (swapRule <$> iUsableRules trs Nothing [t]) `asTypeOf` trs
             | otherwise = \_ -> mapRules swapRule trs

