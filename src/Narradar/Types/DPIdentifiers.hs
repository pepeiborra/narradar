{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}


module Narradar.Types.DPIdentifiers where

import Control.Applicative
import Control.Parallel.Strategies
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Typeable
import Prelude

import Narradar.Types.Term
import Narradar.Framework.Ppr


type Id = Identifier String
type DP a = RuleN (Identifier a)

-- -----------------------
-- Concrete DP Identifiers
-- -----------------------
data Identifier a = IdFunction a | IdDP a | AnyIdentifier deriving (Ord, Typeable)
instance Eq a => Eq (Identifier a) where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False

instance Pretty (Identifier a) => Show (Identifier a) where show = show . pPrint

instance Pretty (Identifier String) where
    pPrint (IdFunction f) = text f
    pPrint (IdDP n) = text n <> text "#"

instance Pretty a => Pretty (Identifier a) where
    pPrint (IdFunction f) = pPrint f
    pPrint (IdDP n) = pPrint n <> text "#"

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

functionSymbol = IdFunction; dpSymbol = IdDP
symbol (IdFunction f) = f; symbol(IdDP f) = f

markDP, unmarkDP :: (MapId t, Functor (t id), DPSymbol id) => Term (t id) v -> Term (t id) v
markDP   = evalTerm return (Impure . mapId markDPSymbol)
unmarkDP = evalTerm return (Impure . mapId unmarkDPSymbol)
returnDP = foldTerm return (Impure . mapId IdFunction)

--unmarkDPRule, markDPRule :: Rule t v -> Rule t v
markDPRule   = fmap markDP
unmarkDPRule = fmap unmarkDP

class DPSymbol s where markDPSymbol, unmarkDPSymbol :: s -> s
instance DPSymbol (Identifier id) where
  markDPSymbol (IdFunction f) = IdDP f
  markDPSymbol f = f
  unmarkDPSymbol (IdDP n) = IdFunction n
  unmarkDPSymbol n = n
