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
import Control.Parallel.Strategies
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
import Text.PrettyPrint

import qualified Language.Prolog.Syntax as Prolog

import Narradar.Term
import Narradar.Utils
import Data.Term
import Data.Term.Rules
import Data.Term.Ppr

type Id = Identifier String
type DP a v = RuleN (Identifier a) v

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

instance Ppr (Identifier a) => Show (Identifier a) where show = show . ppr

instance Ppr (Identifier String) where
    ppr (IdFunction f) = text f
    ppr (IdDP n) = text n <> text "#"

instance Ppr a => Ppr (Identifier a) where
    ppr (IdFunction f) = ppr f
    ppr (IdDP n) = ppr n <> text "#"

instance NFData a => NFData (Identifier a) where
    rnf (IdFunction f) = rnf f
    rnf (IdDP f)       = rnf f
    rnf AnyIdentifier  = ()

$(derive makeFunctor     ''Identifier)
$(derive makeFoldable    ''Identifier)
$(derive makeTraversable ''Identifier)


-- ------------
-- DP Symbols
-- ------------
isDPSymbol (IdDP _ ) = True
isDPSymbol _         = False
markDPSymbol (IdFunction f) = IdDP f
markDPSymbol f = f
unmarkDPSymbol (IdDP n) = IdFunction n
unmarkDPSymbol n = n

functionSymbol = IdFunction; dpSymbol = IdDP
symbol (IdFunction f) = f; symbol(IdDP f) = f

markDP, unmarkDP :: (MapId f, Functor (f (Identifier id))) => Term (f (Identifier id)) v -> Term (f (Identifier id)) v
markDP   = evalTerm return (Impure . mapId markDPSymbol)
unmarkDP = evalTerm return (Impure . mapId unmarkDPSymbol)
returnDP = foldTerm return (Impure . mapId IdFunction)

--unmarkDPRule, markDPRule :: Rule t v -> Rule t v
markDPRule   = fmap markDP
unmarkDPRule = fmap unmarkDP

