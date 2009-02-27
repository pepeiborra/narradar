
{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module DPairs where

import Control.Applicative
import qualified Data.Array.IArray as A
import qualified Data.Graph as G
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable
import qualified Data.Tree as Tree
import Text.XHtml (toHtml, Html)
import Prelude as P

import MonadSupply
import Types
import Utils
import TRS
import Proof

mkDpProblem :: DPMark f id => ProblemType id -> NarradarTRS id f -> ProblemG id f
mkDpProblem Rewriting   trs = mkProblem Rewriting   trs (tRS $ getPairs trs)
mkDPProblem Narrowing   trs = mkProblem Narrowing   trs (tRS $ getNPairs trs)
mkDPProblem BNarrowing  trs = mkProblem BNarrowing  trs (tRS $ getPairs trs)
mkDPProblem LBNarrowing trs = mkProblem LBNarrowing trs (tRS $ getPairs trs)

getPairs :: (Ord id, DPMark f id) => NarradarTRS id f -> [DP f]
getPairs trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isDefined trs) r]

getNPairs :: (Ord id, DPMark f id) => NarradarTRS id f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: (Ord id, DPMark f id) => NarradarTRS id f -> [DP f]
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined trs lp]


{-# SPECIALIZE cycleProcessor :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE sccProcessor   :: Problem BBasicId -> ProblemProof Html BBasicId #-}
cycleProcessor, sccProcessor :: (Bottom :<: f, T id :<: f, DPMark f id, Ord id) => ProblemG id f -> ProblemProofG id Html f
usableSCCsProcessor :: forall f id. (Bottom :<: f, T (Labelled id) :<: f, DPMark f (Labelled id), DPSymbol id, Ord id) => ProblemG (Labelled id) f -> ProblemProofG (Labelled id) Html f

usableSCCsProcessor problem@(Problem typ@(goal -> Just(T goalf tt)) trs dps)
  | null cc   = success (UsableGraph gr reachable) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (UsableGraph gr reachable) problem
                 [return $ Problem typ trs (tRS$ map (rules dps !!) ciclo) | ciclo <- cc, any (`Set.member` reachable) ciclo ]
  where
   gr          = getEDG problem
   cc          = filter isCycle (map Tree.flatten (G.scc gr))
   reachable   = Set.fromList (G.reachable gr =<< goal_pairs)
   goal_pairs  = [ i | (i,r) <- [0..] `zip` rules dps, rootSymbol (lhs r) == Just (Labelling [ j | (j,G) <- zip [1..] tt] (dpSymbol goalf :: id))]
   isCycle [n] = n `elem` gr A.! n
   isCycle _   = True

usableSCCsProcessor p = sccProcessor p

sccProcessor problem@(Problem typ trs dps)
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (tRS$ map (rules dps !!) ciclo) | ciclo <- cc]
    where gr = getEDG problem
          cc = filter isCycle (map Tree.flatten (G.scc gr))
          isCycle [n] = n `elem` gr A.! n
          isCycle _   = True

cycleProcessor problem@(Problem typ trs dps@TRS{})
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (tRS$ map (rules dps !!) ciclo) | ciclo <- cc]
    where cc = cycles gr
          gr = getEDG problem

getEDG :: (Ord id, DPMark f id) => ProblemG id f -> G.Graph
getEDG (Problem typ trs (rules->dps)) | isBNarrowing typ =
    G.buildG (0, length dps - 1)
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain t u | [t'] <- variant' [icap trs $ t] [u] = isJust (unify t' u)

getEDG (Problem typ trs (rules->dps)) =
    G.buildG (0, length dps - 1)
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain t u | [t'] <- variant' [ren $ icap trs $ t] [u] = isJust (unify u t')

ren :: (Var :<: f, HashConsed f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

cap,icap :: forall f id. DPMark f id => NarradarTRS id f -> Term f -> Term f
cap trs t | Just (T (s::id) tt) <- open t
                = term s [if isDefined trs t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
          | otherwise = t

icap trs t | Just (T (s::id) tt) <- open t
                = term s [if any (unifies t' . lhs) (rules trs) then var i else t'
                       | (i,t') <- [0..] `zip` tt]
          | otherwise = t
