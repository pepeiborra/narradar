
{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module DPairs where

import Control.Applicative
import qualified Data.Array.IArray as A
import qualified Data.Graph as G
import Data.Maybe
import Data.Traversable
import qualified Data.Tree as Tree
import Text.XHtml (toHtml, Html)
import Prelude as P

import MonadSupply
import Utils
import Types
import TRS
import Proof

{-# SPECIALIZE graphProcessor :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE graphProcessor :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
graphProcessor :: (Bottom :<: f, T id :<: f, DPMark f id, Ord id) => ProblemG id f -> ProblemProofG id Html f

graphProcessor problem@(Problem typ@(getGoalAF -> Just _) trs dps)
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (tRS$ map (rules dps !!) ciclo) | ciclo <- cc]
    where gr = getEDG problem
          cc = filter isCycle (map Tree.flatten (G.scc gr))
          isCycle [n] = n `elem` gr A.! n
          isCycle _   = True

graphProcessor problem@(Problem typ trs dps@TRS{})
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (tRS$ map (rules dps !!) ciclo) | ciclo <- cc]
    where cc = cycles gr
          gr = getEDG problem


getPairs :: (Ord id, DPMark f id) => NarradarTRS id f -> [DP f]
getPairs trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isDefined trs) r]

getNPairs :: (Ord id, DPMark f id) => NarradarTRS id f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: (Ord id, DPMark f id) => NarradarTRS id f -> [DP f]
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined trs lp]

getEDG :: (Ord id, DPMark f id) => ProblemG id f -> G.Graph
getEDG (Problem typ trs (rules->dps)) | isBNarrowing typ =
    G.buildG (0, length dps - 1)
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain t u | [t'] <- variant' [cap trs $ t] [u] = isJust (unify t' u)

getEDG (Problem typ trs (rules->dps)) =
    G.buildG (0, length dps - 1)
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain t u | [t'] <- variant' [ren $ cap trs $ t] [u] = isJust (unify u t')

ren :: (Var :<: f, HashConsed f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

cap :: forall f id. DPMark f id => NarradarTRS id f -> Term f -> Term f
cap trs t | Just (T (s::id) tt) <- open t
                = term s [if isDefined trs t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
          | otherwise = t
