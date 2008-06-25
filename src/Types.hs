{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
module Types (module TRS, module Types) where

import Data.AlaCarte
import Data.Foldable (Foldable)
import Data.List ((\\))
import Data.Traversable
import Unsafe.Coerce
import TRS

import Utils
import Prelude as P

class (T Identifier :<: f, Var :<: f, Traversable f) => TRSC f
instance (T Identifier :<: f, Var :<: f, Traversable f) => TRSC f

data TRS f = (TRSC f, MatchShapeable f, Unifyable f, Eq (f(Expr f))) => TRS [Rule f]
type  DP a = Rule a

fromTRS (TRS trs) = trs

instance Ppr f => Show (TRS f) where show (TRS trs) = show trs

mkTRS :: [Rule (T String :+: Var) ] -> TRS (T Identifier :+: Var)
mkTRS rules = TRS (fmap2 (foldTerm f) rules) where
  f :: (T String :<: tstring, T Identifier :<: tident) => tstring (Term tident) -> Term tident
  f t
     | Just(T f tt) <- prj t = term (IdFunction f) tt
     | otherwise = inject (unsafeCoerce t :: tident(Term tident))


{-
class MkTRS f where mkTRSF :: f(Term g) -> (Term (Subst g (T String) (T Identifier)))
instance MkTRS Var Var where mkTRSF = inject (unsafeCoerce t :: f(Term )
-}

rootSymbol :: (T Identifier :<: f) => Term f -> Maybe Identifier
rootSymbol t | Just (T root _) <- match t = Just root
             | otherwise = Nothing

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

class (Var :<: f) => ExtraVars t f | t -> f where extraVars :: t -> [Var (Term f)]
instance (Var :<: f) => ExtraVars (TRS f) f where extraVars (TRS trs) = concat [vars r \\ vars l | l :-> r <- trs]
instance (Var :<: f, Foldable f) => ExtraVars (Rule f) f where extraVars (l:->r) = vars r \\ vars l