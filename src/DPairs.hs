{-# LANGUAGE PatternSignatures, PatternGuards #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module DPairs where

import Control.Applicative
import Data.AlaCarte
import qualified Data.Graph.Inductive as G
import Data.Maybe
import Data.Traversable
import Text.XHtml (toHtml, Html)
import Prelude as P

import MonadSupply
import Problem
import Utils
import Types

cycleProcessor :: Problem f -> ProblemProgress Html f
cycleProcessor problem@(Problem typ trs@TRS{} dps)
  | null cc   = Success DependencyGraph problem (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  And DependencyGraph problem [NotDone $ Problem typ trs  (tRS$ map (rules dps !!) ciclo) | ciclo <- cc]
    where cc = cycles $ getEDG trs (rules dps)


getPairs :: TRS f -> [DP f]
getPairs trs@TRS{} =
    [ markDP l :-> markDP rp| l :-> r <- rules trs, rp <- collect (isDefined (rules trs)) r ]

getNPairs :: TRS f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: TRS f -> [DP f]
getLPairs trs@TRS{} = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined (rules trs) lp]

getEDG :: TRS f -> [DP f] -> G.Gr () ()
getEDG trs@TRS{} dps = G.mkUGraph [0.. length dps - 1]
                           [ (i,j) | (i,_:->t) <- zip [0..] dps
                                   , (j,u:->_) <- zip [0..] dps
                                   , inChain t u]
    where inChain t u = isJust (unify t (ren $ cap trs $ u))

ren :: (Var :<: f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

--cap :: (MatchShapeable f, T IdFunctions :<: f, Foldable f, Var :<: f) => TRS sig f -> Expr f -> Term f
cap :: TRS f -> Expr f -> Term f
cap trs@TRS{} t | Just (T (s::Identifier) tt) <- match t
                = term s [if isDefined (rules trs) t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
                | otherwise = t
