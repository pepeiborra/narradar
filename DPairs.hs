module DPairs where

import Control.Applicative
import Data.AlaCarte
import Data.Foldable
import qualified Data.Graph.Inductive as G
import Data.Traversable
import Prelude as P

import Types
import MonadSupply

--getPairs :: (Var :<: f, T IdFunctions :<: f, T IdDPs :<: f, MatchShapeable f, Foldable f) => TRS sig f -> [Rule f]
getPairs (TRS rules) =
    [ markDP l :-> markDP rp| l :-> r <- rules, rp <- collect (isDefined rules) r ]

getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs (TRS rules) = [ markDP l :-> markDP lp| l :-> _ <- rules, lp <- properSubterms l, isDefined rules lp]

--getEDG ::(Var :<: f, T IdFunctions :<: f, MatchShapeable f, Traversable f, Unifyable f) => TRS sig f -> [DP f] -> G.Gr () ()
getEDG trs dps = G.mkUGraph [0.. length dps - 1]
                           [ (i,j) | (i,_:->t) <- zip [0..] dps
                                   , (j,u:->_) <- zip [0..] dps
                                   , inChain t u]
    where inChain t u =  t `equal` (ren $ cap trs $ u)

ren :: (Var :<: f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

--cap :: (MatchShapeable f, T IdFunctions :<: f, Foldable f, Var :<: f) => TRS sig f -> Expr f -> Term f
cap trs t | Just (T (s::IdFunctions) tt) <- match t
         = term s [if isDefined trs t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
         | otherwise = t
