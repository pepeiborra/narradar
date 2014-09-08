{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric #-}
{-# LANGUAGE CPP #-}


module Narradar.Types.DPIdentifiers
    (module Narradar.Types.DPIdentifiers, ArityId(..), StringId
    )  where

import Control.Applicative
import Control.Arrow (first)
import Control.DeepSeq
import Control.Monad.Free
import qualified Data.ByteString.Char8 as BS
import Data.Foldable (Foldable(..))
import Data.Hashable
import Data.Traversable (Traversable(..))
import Data.Typeable
import Prelude

import Narradar.Types.Term
import Narradar.Framework.Ppr

import GHC.Generics (Generic)
import Debug.Hoed.Observe

type Id = DPIdentifier StringId
type DP a = RuleN (DPIdentifier a)

-- -----------------------
-- Concrete DP Identifiers
-- -----------------------
data DPIdentifier a = IdFunction a | IdDP a | AnyIdentifier
                    deriving (Ord, Typeable, Functor, Foldable, Traversable, Generic,Generic1)
instance Eq a => Eq (DPIdentifier a) where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False

instance HasArity a => HasArity (DPIdentifier a) where
    getIdArity (IdFunction f) = getIdArity f
    getIdArity (IdDP f)       = getIdArity f
    getIdArity AnyIdentifier  = 0

instance Pretty (DPIdentifier a) => Show (DPIdentifier a) where show = show . pPrint

instance Pretty (DPIdentifier String) where
    pPrint (IdFunction f) = text f
    pPrint (IdDP n) = text n <> text "#"

instance Pretty a => Pretty (DPIdentifier a) where
    pPrint (IdFunction f) = pPrint f
    pPrint (IdDP n) = pPrint n <> text "#"

instance NFData a => NFData (DPIdentifier a) where
    rnf (IdFunction f) = rnf f
    rnf (IdDP f)       = rnf f
    rnf AnyIdentifier  = ()

instance Hashable a => Hashable (DPIdentifier a) where
    hashWithSalt s (IdFunction f) = hashWithSalt s f
    hashWithSalt s (IdDP f) = hashWithSalt 1 (hashWithSalt s f)

instance Observable (DPIdentifier String)   where observer  x = send (show x) (return x)
instance Observable (DPIdentifier StringId) where observer  x = send (show x) (return x)
instance Observable1 DPIdentifier           -- where observer1 x = send "NO WAY" (return x)
instance Observable a => Observable(DPIdentifier a) where
  observer = observer1 ; observers = observers1

-- ------------
-- DP Symbols
-- ------------

class DPSymbol s where
  markDPSymbol, unmarkDPSymbol :: s -> s
  isDPSymbol :: s -> Bool

instance DPSymbol (DPIdentifier id) where
  markDPSymbol (IdFunction f) = IdDP f
  markDPSymbol f              = f
  unmarkDPSymbol (IdDP n) = IdFunction n
  unmarkDPSymbol n        = n
  isDPSymbol (IdDP _ ) = True
  isDPSymbol _         = False

functionSymbol = IdFunction; dpSymbol = IdDP
symbol (IdFunction f) = f; symbol(IdDP f) = f

--markDP, unmarkDP :: (MapId t, Functor (t id), DPSymbol id) => Term (t id) v -> Term (t id) v
markDP   = evalTerm return (Impure . mapId markDPSymbol)
unmarkDP = evalTerm return (Impure . mapId unmarkDPSymbol)
returnDP = foldTerm return (Impure . mapId IdFunction)

--unmarkDPRule, markDPRule :: Rule t v -> Rule t v
markDPRule   = fmap markDP
unmarkDPRule = fmap unmarkDP
