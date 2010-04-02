{-# LANGUAGE TypeFamilies #-}

module Narradar.Constraints.Syntactic where

import Data.Foldable (Foldable)
import Data.Maybe (catMaybes)
import Narradar.Types

import qualified Data.Set as Set

isConstructorBased :: (HasRules t v trs, HasSignature trs, HasId t, Foldable t, SignatureId trs ~ TermId t) => trs -> Bool
isConstructorBased trs = all (isConstructorRule trs) (rules trs)


isConstructorRule sig = Set.null
                      . Set.intersection (getDefinedSymbols sig)
                      . Set.fromList . catMaybes . map rootSymbol . properSubterms . lhs