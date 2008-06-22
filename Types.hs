{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, GADTs #-}
module Types (module TRS, module Types) where

import Data.AlaCarte
import Data.List ((\\))
import Data.Traversable
import TRS

import Utils
import Prelude as P

class (T Identifier :<: f, Var :<: f, Traversable f) => TRSC f
instance (T Identifier :<: f, Var :<: f, Traversable f) => TRSC f

data TRS f = (TRSC f, MatchShapeable f, Unifyable f) => TRS [Rule f]
type  DP a = Rule a

fromTRS (TRS trs) = trs

instance Ppr f => Show (TRS f) where show (TRS trs) = show trs

mkTRS :: [Rule (T String :+: Var) ] -> TRS (T Identifier :+: Var)
mkTRS rules = TRS (fmap2 (foldTerm f) rules)
    where f t | Just(Var i) <- prj t = var i
              | Just(T f tt)<- prj t = term (IdFunction f) tt

markDPSymbol (IdFunction f) = IdDP f
markDPSymbol f = f
unmarkDPSymbol (IdDP n) = IdFunction n
unmarkDPSymbol n = n

markDP, unmarkDP :: (T Identifier :<: f) => Term f -> Term f
markDP t | Just (T (n::Identifier) tt) <- match t = term (markDPSymbol n) tt
         | otherwise                = t
unmarkDP t | Just (T (n::Identifier) tt) <- match t = term (unmarkDPSymbol n) tt
           | otherwise                = t

unmarkDPRule, markDPRule :: (T Identifier :<: f) => Rule f -> Rule f
markDPRule   = fmap   markDP
unmarkDPRule = fmap unmarkDP

data Identifier = IdFunction String | IdDP String
  deriving (Eq, Ord)

instance Show Identifier where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

hasExtraVars :: TRS f -> Bool
hasExtraVars (TRS trs) = not $ P.all null [vars r \\ vars l | l :-> r <- trs]
