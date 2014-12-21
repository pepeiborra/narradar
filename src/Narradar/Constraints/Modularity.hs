{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.Constraints.Modularity where

import Data.Foldable (Foldable,toList)
import Data.List ((\\), partition)
import Data.Array as A
import qualified Data.Graph as G
import Data.Graph.SCC
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Set as Set
import Narradar.Types hiding ((<>))

import qualified Data.Term.Family as Family
import Debug.Hoed.Observe (Observable)

makeHierarchicalCombination :: ( id ~ Family.Id ex
                               , ex ~ base
                               , HasSignature ex, HasId ex
                               , Ord id
                               ) => [RuleF ex] -> [RuleF base] -> ([RuleF ex],[RuleF base])

makeHierarchicalCombination ex base =
    partition (maybe True (`Set.member` exSymbols') . getId . lhs) allRules
  where
    exSymbols' =
      Set.fromList $ concat
      [ map (allDefSymbols A.!) scc
            | scc <- map G.flattenSCC $ sccList callGraph
            , not $ Set.null (Set.fromList scc `Set.intersection` exSymbols)
            ]

    exSymbols = Set.fromList [ i | let s = getDefinedSymbols ex
                                 , (i,g) <- assocs allDefSymbols
                                 , Set.member g s]

    callGraph = G.buildG (bounds allDefSymbols)
                         [ (i,j) | (i,f) <- assocs allDefSymbols
                                 , (j,g) <- assocs allDefSymbols
                                 , f /= g
                                 , any ( (g `Set.member`)  . getAllSymbols . rhs)
                                       (getRulesFor f)
                                 ]
    all = ex <> base
    allDefSymbols = let s = toList(getDefinedSymbols all) in listArray (0, length s -1 ) s
    allRules = rules all
    getRulesFor f = filter ( (== Just f) . getId . lhs) allRules

--isHierarchicalCombination :: (HasSignature trs1, HasSignature trs2) => trs1 -> trs2 -> Bool
isHierarchicalCombination :: ( HasSignature ex, HasSignature base
                             , Family.Id ex ~ Family.Id base
                             , Ord(Family.Id base)
                             ) => ex -> base -> Bool
isHierarchicalCombination ex base =
  Set.null(getDefinedSymbols base `Set.intersection` getDefinedSymbols ex) &&
  Set.null(getConstructorSymbols base `Set.intersection` getDefinedSymbols ex)

isRelaxedHierarchicalCombination :: (HasSignature trs, HasRules trs
                                    ,Family.Id t ~ Family.Id trs
                                    ,Rule t v ~ Family.Rule trs
                                    ,HasId1 t, Unify t
                                    ,Observable(Term t v), Observable v
                                    ,Ord v
                                    ,Ord (Family.Id trs)
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

isGeneralizedHierarchicalCombination :: ( HasSignature trs, HasRules trs, Ord (Term t v)
                                        , Rule t v ~ Family.Rule trs
                                        , HasId1 t, Match t, Traversable t
                                        , Enum v, Ord v, Rename v, Observable v
                                        , Family.Id t ~ Family.Id trs
                                        , Ord(Family.Id trs)
                                        ) => trs -> trs -> Bool
isGeneralizedHierarchicalCombination ex base =
-- A generalized hierarchical combination is an HC with shared rules
  isHierarchicalCombination ex' base' &&
  -- All the rules for a shared symbol must exist on both systems
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
  :: ( HasSignature trs
     , HasRules trs
     , Rule t v ~ Family.Rule trs
     , Family.Id trs ~ Family.Id t
     , Ord (Term t v)
     , HasId1 t, Unify t, Traversable t
     , Enum v, Ord v, Rename v
     , Observable v, Observable(Term t v)
     , Ord(Family.Id trs)
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

isHTtrs ex base = all (\(_ :-> r) -> isHT_ r) (rules ex)
  where
      isHT_ = isHT (getSignature ex) (getSignature base)


isHT :: (HasId1 f, Foldable f, Ord(Family.Id f)
        ) => Signature (Family.Id f) -> Signature (Family.Id f) -> Term f v -> Bool
isHT exsig basesig = go
 where
  go t
    | Just f <- rootSymbol t
    , f `Set.member` d_ex
    = all go (directSubterms t)
    | Just f <- rootSymbol t
    , f `Set.member` d_b
    = t `notFrom` d_ex && all go (directSubterms t)
    | Just _ <- rootSymbol t
    = all go (directSubterms t)
    | otherwise = True

  d_ex = Map.keysSet $ definedSymbols exsig
  d_b  = Map.keysSet $ definedSymbols basesig
  term `notFrom` symbols =
    Set.null (Set.fromList(toList(getSignature term)) `Set.intersection` symbols)
