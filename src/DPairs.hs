{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module DPairs where

import Control.Applicative
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.PatriciaTree
import Data.Maybe
import Data.Traversable
import Text.XHtml (toHtml, Html)
import Prelude as P

import MonadSupply
import Utils
import Types
import TRS
import Proof

cycleProcessor :: Zip f => Problem f -> ProblemProof Html f
cycleProcessor problem@(Problem typ trs@TRS{} dps)
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (tRS'$ map (rules dps !!) ciclo) | ciclo <- cc]
    where cc = cycles gr
          gr = getEDG problem


getPairs :: TRS Identifier f -> [DP f]
getPairs trs@TRS{} =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isDefined (rules trs)) r]

getNPairs :: TRS Identifier f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: TRS Identifier f -> [DP f]
getLPairs trs@TRS{} = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined (rules trs) lp]

getEDG :: Problem f -> UGr
getEDG (Problem typ trs@TRS{} (rules->dps)) | isBNarrowing typ =
    G.mkUGraph [0.. length dps - 1]
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain t u | [t'] <- variant' [cap trs $ t] [u] = isJust (unify t' u)

getEDG (Problem typ trs@TRS{} (rules->dps)) =
    G.mkUGraph [0.. length dps - 1]
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain t u | [t'] <- variant' [ren $ cap trs $ t] [u] = isJust (unify u t')

ren :: (Var :<: f, HashConsed f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

--cap :: (Zip f, T IdFunctions :<: f, Foldable f, Var :<: f) => TRS sig f -> Term f -> Term f
cap :: TRS Identifier f -> Term f -> Term f
cap trs@TRS{} t | Just (T (s::Identifier) tt) <- open t
                = term s [if isDefined (rules trs) t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
                | otherwise = t
