{-# LANGUAGE TypeFamilies #-}

module Narradar.Constraints.Syntactic where

import Data.Foldable (Foldable)
import Data.Maybe (catMaybes, maybeToList)

import Narradar.Types

import qualified Data.Set as Set

nonLeftLinearRules :: (Ord v, Foldable t, Functor t, HasRules t v trs) => trs -> [Rule t v]
nonLeftLinearRules trs = [ l:->r | l:->r <- rules trs, not (isLinear l)]

isConstructorBased :: (HasRules t v trs, HasSignature trs, HasId t, Foldable t, SignatureId trs ~ TermId t) => trs -> Bool
isConstructorBased trs = all (isConstructorRule trs) (rules trs)


isConstructorRule sig = Set.null
                      . Set.intersection (getDefinedSymbols sig)
                      . Set.fromList . catMaybes . map rootSymbol . properSubterms . lhs

criticalPairs :: (HasRules t v trs, Enum v, Ord v, Rename v, Unify t) =>
                 trs -> [(Position, Term t v, Term t v)]
criticalPairs trs
   | null (rules trs) = []
   | otherwise        = -- Overlays between distinct rules
                        [ (p, updateAt p (const r') l \\ sigma, r \\ sigma)
                             | (l :-> r,rest)  <- view (rules trs)
                             , l' :-> r' <- (`getVariant` (l:->r)) `map` rules rest
                             , l_p@Impure{} <- subterms $ annotateWithPos l
                             , let p = note l_p
                             , sigma <- maybeToList $ unify (dropNote l_p) l'
                        ] ++
                        -- Overlays inside the same rule
                        [ (p, updateAt p (const r') l \\ sigma, r \\ sigma)
                             | l :-> r <- rules trs
                             , let l' :-> r' = getVariant (l:->r) (l:->r)
                             , l_p@Impure{} <- properSubterms $ annotateWithPos l
                             , let p = note l_p
                             , sigma <- maybeToList $ unify (dropNote l_p) l'
                        ]
  where
   t \\ sigma = applySubst sigma t
   -- comonadic map??? Need to learn about comonads
   view = go [] where
      go acc [x]    = [(x,acc)]
      go acc (x:xx) = (x, acc ++ xx) : go (x:acc) xx