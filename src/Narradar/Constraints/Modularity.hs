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

isRelaxedHierarchicalCombination :: (HasSignature trs, HasRules t v trs
                                    ,TermId t ~ SignatureId trs
                                    ,HasId t, Unify t
                                    ,Ord v
                                    ) => trs -> trs -> Bool
isRelaxedHierarchicalCombination ex base =
  Set.null(getDefinedSymbols base `Set.intersection` getDefinedSymbols ex) &&
  everyExtensionCallIsARigidHeadNF
 where
   everyExtensionCallIsARigidHeadNF
      = all isRHNF [ rp | l:->r  <- rr
                        , rp     <- subterms r
                        , Just f <- [rootSymbol rp]
                        , f `Set.member` getDefinedSymbols ex]
   rr = rules base
   isRHNF t = not $ any (unifies t) (map lhs rr)

isGeneralizedHierarchicalCombination :: ( HasSignature trs, HasRules t v trs, Ord (Term t v)
                                        , HasId t, Match t, Traversable t, Enum v, Ord v, Rename v
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

isGeneralizedRelaxedHierarchicalCombination
  :: ( HasSignature trs, TermId t ~ SignatureId trs
     , HasRules t v trs
     , Ord (Term t v)
     , HasId t, Unify t, Traversable t
     , Enum v, Ord v, Rename v
     ) => trs -> trs -> Bool
isGeneralizedRelaxedHierarchicalCombination ex base =
  isRelaxedHierarchicalCombination ex' base' &&
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
