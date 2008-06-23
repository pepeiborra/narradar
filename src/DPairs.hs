{-# LANGUAGE PatternSignatures, PatternGuards #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module DPairs where

import Control.Applicative
import Data.AlaCarte
import qualified Data.Graph.Inductive as G
import Data.Maybe
import Data.Traversable
import Prelude as P

import MonadSupply
import Problem
import Utils
import Types

cycleProcessor :: Problem f -> ProblemProgress s f
cycleProcessor problem@(Problem typ trs (TRS dps)) =
    And DependencyGraph problem [NotDone $ Problem typ trs  (TRS$ map (dps !!) ciclo) | ciclo <- cc]
    where cc = cycles $ getEDG trs dps


getPairs :: TRS f -> [DP f]
getPairs (TRS rules) =
    [ markDP l :-> markDP rp| l :-> r <- rules, rp <- collect (isDefined rules) r ]

getNPairs :: TRS f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: TRS f -> [DP f]
getLPairs (TRS rules) = [ markDP l :-> markDP lp | l :-> _ <- rules, lp <- properSubterms l, isDefined rules lp]

getEDG :: TRS f -> [DP f] -> G.Gr () ()
getEDG trs@TRS{} dps = G.mkUGraph [0.. length dps - 1]
                           [ (i,j) | (i,_:->t) <- zip [0..] dps
                                   , (j,u:->_) <- zip [0..] dps
                                   , inChain t u]
    where inChain t u =  isJust (unify t (ren $ cap trs $ u))

ren :: (Var :<: f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

--cap :: (MatchShapeable f, T IdFunctions :<: f, Foldable f, Var :<: f) => TRS sig f -> Expr f -> Term f
cap :: TRS f -> Expr f -> Term f
cap (TRS trs) t | Just (T (s::Identifier) tt) <- match t
                = term s [if isDefined trs t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
                | otherwise = t
