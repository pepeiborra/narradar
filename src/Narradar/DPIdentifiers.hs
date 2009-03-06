{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}


module Narradar.DPIdentifiers where

import Control.Applicative
import Control.Arrow
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.HashTable (hashString)
import Data.Foldable (toList, Foldable(..))
import Data.Int
import Data.List (isSuffixOf)
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Traversable (Traversable(..))
import Prelude

import TRS

import Narradar.Utils
import Narradar.Bottom

type Id = Identifier String

-- -----------------------
-- Concrete DP Identifiers
-- -----------------------
data Identifier a = IdFunction a | IdDP a | AnyIdentifier deriving (Ord)
instance Eq a => Eq (Identifier a) where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False

instance Show (Identifier String) where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

instance Show a => Show (Identifier a) where
    show (IdFunction f) = show f
    show (IdDP n) = show n ++ "#"

$(derive makeFunctor     ''Identifier)
$(derive makeFoldable    ''Identifier)
$(derive makeTraversable ''Identifier)

-- -----------------------
-- Named Term Signatures
-- -----------------------

type Basic'   = Var :+: T String :+: Hole
type BBasic   = Var :+: T String :+: Hole :+: Bottom
type BasicId  = Var :+: T Id :+: Hole
type BBasicId = Var :+: T Id :+: Hole :+: Bottom
instance HashConsed BBasicId
instance HashConsed BasicId
instance HashConsed BBasic
instance HashConsed Basic'
instance HashConsed (T Id)

-- ------------
-- DP Symbols
-- ------------
{-
class (Show id, Ord id) => DPSymbol id where
  markDPSymbol, unmarkDPSymbol :: id -> id
  functionSymbol, dpSymbol :: String -> id
  isDPSymbol   :: id -> Bool
  isDPSymbol s = markDPSymbol s == s
--  symbol :: id -> String
-}
--instance DPSymbol Identifier where

isDPSymbol (IdDP _ ) = True
isDPSymbol _         = False
markDPSymbol (IdFunction f) = IdDP f
markDPSymbol f = f
unmarkDPSymbol (IdDP n) = IdFunction n
unmarkDPSymbol n = n
functionSymbol = IdFunction; dpSymbol = IdDP
symbol (IdFunction f) = f; symbol(IdDP f) = f

markDP = mapTerm markDPF; unmarkDP = mapTerm unmarkDPF
class (TRSC f, DPMark' f f) => DPMark f; instance (TRSC f, DPMark' f f) => DPMark f
class (f :<: g) => DPMark' f g where markDPF, unmarkDPF :: f(Term g) -> Term g

instance (T (Identifier id) :<: g) => DPMark' (T (Identifier id)) g where
    markDPF   (T n tt) = term (markDPSymbol n) tt
    unmarkDPF (T n tt) = term (unmarkDPSymbol n) tt
instance (DPMark' a g, DPMark' b g, (a:+:b) :<: g) => DPMark' (a:+:b) g where
    markDPF (Inl x) = markDPF x; markDPF(Inr x) = markDPF x
    unmarkDPF (Inl x) = unmarkDPF x; unmarkDPF(Inr x) = unmarkDPF x
instance (t :<: g) => DPMark' t g where markDPF = inject; unmarkDPF = inject

unmarkDPRule, markDPRule :: DPMark f => Rule f -> Rule f
markDPRule   = fmap markDP
unmarkDPRule = fmap unmarkDP

-- -------------------
-- Various stuff
-- -------------------

instance Show id => HashTerm (T id) where hashF (T id tt) = 14 * sum tt * hashId id

type family   DPVersionOf (f :: * -> *) :: * -> *
type instance DPVersionOf (T id)    = T (Identifier id)
type instance DPVersionOf Var       = Var
type instance DPVersionOf (a :+: b) = (DPVersionOf a :+: DPVersionOf b)
type instance DPVersionOf Bottom    = Bottom
type instance DPVersionOf Hole      = Hole


-- -------------------
-- Failed attempts
-- -------------------
{-
convert = foldTerm convertF

class (Functor f, TRSC g) => Convert f g where convertF :: f (Term g) -> Term g
instance TRSC f => Convert f f where convertF = In
instance (T Identifier :<: g, TRSC g) => Convert (T String) g where
    convertF (T f tt) = term (IdFunction f) tt
instance (Convert f1 g, Convert f2 g) => Convert (f1 :+: f2) g where
    convertF (Inl x) = convertF x
    convertF (Inr x) = convertF x
instance (a :<: g, TRSC g) => Convert a g where convertF t = inject(fmap reinject t)
-}


{-
class LabelWith a where
  type result a
  labelWith :: a -> [Int] -> result

instance LabelWith (Labelled a) where
    -}
