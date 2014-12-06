{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.Constraints.Syntactic where

import Data.Foldable (Foldable)
import Data.Maybe (catMaybes, maybeToList)

import Narradar.Types

import qualified Data.Set as Set
import qualified Data.Term.Family as Family

isLeftLinear :: (Ord v, Foldable t, Functor t, HasRules trs, Rule t v ~ Family.Rule trs) => trs -> Bool
isLeftLinear = null . nonLeftLinearRules

isNonDuplicatingTRS = null . duplicatingRules

duplicatingRules :: (HasRules a, Foldable termF, Ord v, Functor termF, Family.Rule a ~ RuleF (Term termF v)) => a -> [RuleF (Term termF v)]
duplicatingRules = filter isDuplicating . rules

nonLeftLinearRules :: (Ord v, Foldable t, Functor t, HasRules trs, Rule t v ~ Family.Rule trs) => trs -> [Rule t v]
nonLeftLinearRules trs = [ l:->r | l:->r <- rules trs, not (isLinear l)]

isConstructorBased :: (HasRules trs, Rule t v ~ Family.Rule trs, HasSignature trs, HasId1 t, Foldable t, Family.Id trs ~ Family.Id t) => trs -> Bool
isConstructorBased trs = all (isConstructorRule trs) (rules trs)

isConstructorRule sig = Set.null
                      . Set.intersection (getDefinedSymbols sig)
                      . Set.fromList . catMaybes . map rootSymbol . properSubterms . lhs
