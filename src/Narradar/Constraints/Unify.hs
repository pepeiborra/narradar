module Narradar.Constraints.Unify where

import Control.Exception (assert)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Term hiding (unify, unifies)
import qualified Data.Term as Term
import Narradar.Types.Term

unifies  x y = isJust (unify x y)
unifies' x y = isJust (unify' x y)
matches' x y = isJust (match' x y)

unify :: (Ord v, Unify t) => Term t v -> Term t v -> Maybe(Substitution t v)
unify = Term.unify

unify' w s = let s' = variant s w in maybe (fail "unify'") return (unify w s')
match' w s = let s' = variant s w in maybe (fail "match'") return (match w s')
getUnifier' w s = let s' = getVariant s w in maybe (fail "getUnifier'") return (getUnifier w s')


applySubst (Subst s) = assert (not infinite) $ Term.applySubst (zonkSubst $ Subst s)
  where infinite = or [ v `elem` vars t | (v,t) <- Map.toList s]
