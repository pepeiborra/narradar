{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.Constraints.Modularity where

import Data.List ((\\))
import Data.Traversable (Traversable)
import qualified Data.Set as Set
import Narradar.Types

isHierarchicalCombination :: HasSignature trs => trs -> trs -> Bool
isHierarchicalCombination ex base =
  Set.null(getDefinedSymbols base `Set.intersection` getDefinedSymbols ex) &&
  Set.null(getConstructorSymbols base `Set.intersection` getDefinedSymbols ex)

isGeneralizedHierarchicalCombination :: ( HasSignature trs, HasRules t v trs, Ord (Term t v)
                                        , HasId t, Match t, Traversable t, Enum v, Ord v
                                        , TermId t ~ SignatureId trs
                                        ) => trs -> trs -> Bool
isGeneralizedHierarchicalCombination ex base =
  isHierarchicalCombination ex' base' &&
  all (\rE -> any (equiv2' rE) baseShared) exShared &&
  all (\rB -> any (equiv2' rB) exShared) baseShared
 where
    sharedSymbols = getDefinedSymbols base `Set.intersection` getDefinedSymbols ex
    exShared      = rulesFor sharedSymbols ex
    baseShared    = rulesFor sharedSymbols base
    ex'   = rules ex \\ exShared
    base' = rules base \\ baseShared
    rulesFor ids trs = [ r | r <- rules trs
                                 , Just id <- [rootSymbol (lhs r)]
                                 , id `Set.member` ids]