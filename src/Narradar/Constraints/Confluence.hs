{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
module Narradar.Constraints.Confluence where

import Data.Foldable (Foldable)
import Data.Maybe (catMaybes, maybeToList, listToMaybe)
import Data.Term (equiv)
import Data.Term.Rewriting

import Narradar.Constraints.Syntactic
import Narradar.Types

import qualified Data.Set as Set
import qualified Data.Term.Family as Family
import Debug.Hoed.Observe (Observable)

isOrthogonal p = isLeftLinear p && null (criticalPairs p)

isAlmostOrthogonal :: ( HasRules trs, GetVars trs
                      , Rule t v ~ Family.Rule trs
                      , v ~ Family.Var trs
                      , Eq (Term t v)
                      , Unify t
                      , Rename v, Enum v, Ord v
                      , Observable v, Observable(Term t v)
                      ) => trs -> Bool
isAlmostOrthogonal p = isLeftLinear p && all isOverlay cps && and[ r1==r2 | (p,r1,r2) <- cps]
    where cps = criticalPairs p

isOverlayTRS p = (all isOverlay . criticalPairs) p

isOverlay ([],r1,r2) = True
isOverlay _ = False

isNonOverlapping p = (null . criticalPairs) p

locallyConfluent :: ( HasRules trs, GetVars trs
                    , Unify t, Ord (Term t v)
                    , Enum v, Ord v, Rename v
                    , Family.Rule trs ~ RuleF (Term t v)
                    , Family.Var trs ~ v
                    , Observable v, Observable(Term t v)
                    ) => trs -> Bool
locallyConfluent p = (all joinable . criticalPairs) p
  where
    joinable (_, s, t) = s == t ||
                         rewritesQuickly s == rewritesQuickly t

    rewritesQuickly t = fmap EqModulo $ listToMaybe $ take 100 $ rewrites (rules p) t

--getOverlay :: Term t v -> Term -> [ (Position, Substitution) ]
getOverlaysGen subterms l l' =
  [ (note l_p, sigma)
  | l_p <- subterms $ annotateWithPos l
  , not (isVar l_p)
  , Just sigma <- [unify (dropNote l_p) l']
  ]

getOverlays x       = getOverlaysGen subterms x
getProperOverlays x = getOverlaysGen properSubterms x

criticalPairsOfGen subterms (l :-> r) rr =
  [ (p, updateAt p (const r') l \\ sigma, r \\ sigma)
  | l' :-> r' <- rr
  , (p,sigma) <- getOverlaysGen subterms l l'
  ]
  where
    t \\ sigma = applySubst sigma t

properCriticalPairsOf x = criticalPairsOfGen properSubterms x
criticalPairsOf x = criticalPairsOfGen subterms x

criticalPairs :: ( HasRules trs, Rule t v ~ Family.Rule trs
                 , v ~ Family.Var trs, GetVars trs, Enum v, Ord v, Rename v, Unify t
                 , Observable v, Observable(Term t v)) =>
                 trs -> [(Position, Term t v, Term t v)]
criticalPairs trs
   | null (rules trs) = []
   | otherwise        = -- Overlays between distinct rules
                        [ cp
                             | (lr,rest)  <- view (rules trs)
                             , let lr' = getVariant lr trs
                             , cp <- criticalPairsOf lr' rest
                        ] ++
                        -- Overlays inside the same rule
                        [ cp
                             | lr <- rules trs
                             , let lr' = getVariant lr lr
                             , cp <- properCriticalPairsOf lr' [lr]
                        ]
  where
   t \\ sigma = applySubst sigma t
   -- comonadic map??? Need to learn about comonads
   view = go [] where
      go acc [x]    = [(x,acc)]
      go acc (x:xx) = (x, acc ++ xx) : go (x:acc) xx
