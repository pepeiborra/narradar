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
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}


module Narradar.Types.DPIdentifiers
    (module Narradar.Types.DPIdentifiers, ArityId(..), StringId
    )  where

import Control.Applicative
import Control.Arrow (first)
import Control.DeepSeq
import Data.Foldable (Foldable(..))
import Data.NarradarTrie (HasTrie, (:->:))
import qualified Data.NarradarTrie as Trie
import Data.Traversable (Traversable(..))
import Data.Typeable
import Prelude

import Narradar.Types.Term
import Narradar.Framework.Ppr


type Id = DPIdentifier StringId
type DP a = RuleN (DPIdentifier a)

-- -----------------------
-- Concrete DP Identifiers
-- -----------------------
data DPIdentifier a = IdFunction a | IdDP a | AnyIdentifier
                    deriving (Ord, Typeable, Functor, Foldable, Traversable)
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

instance HasTrie a => HasTrie (DPIdentifier a) where
  data DPIdentifier a :->: x = DPIdentifierTrie (a :->: x) (a :->: x)
  empty = DPIdentifierTrie Trie.empty Trie.empty
  lookup (IdFunction f) (DPIdentifierTrie dpt ft) = Trie.lookup f ft
  lookup (IdDP dp) (DPIdentifierTrie dpt ft) = Trie.lookup dp dpt
  insert (IdFunction f) v (DPIdentifierTrie dpt ft) = DPIdentifierTrie dpt (Trie.insert f v ft)
  insert (IdDP dp) v (DPIdentifierTrie dpt ft) = DPIdentifierTrie (Trie.insert dp v dpt) ft
  toList (DPIdentifierTrie ft dpt) = map (first IdDP) (Trie.toList dpt) ++
                                     map (first IdFunction)   (Trie.toList ft)
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

markDP, unmarkDP :: (MapId t, Functor (t id), DPSymbol id) => Term (t id) v -> Term (t id) v
markDP   = evalTerm return (Impure . mapId markDPSymbol)
unmarkDP = evalTerm return (Impure . mapId unmarkDPSymbol)
returnDP = foldTerm return (Impure . mapId IdFunction)

--unmarkDPRule, markDPRule :: Rule t v -> Rule t v
markDPRule   = fmap markDP
unmarkDPRule = fmap unmarkDP
