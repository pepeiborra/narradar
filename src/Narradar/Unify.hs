module Narradar.Unify where

import Control.Exception
import Control.Monad
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Term hiding (unify, unifies)
--import Data.Term (variant)
import qualified Data.Term as Term
import Narradar.Term

unifies  x y = isJust (unify x y)
unifies' x y = isJust (unify' x y)

unify :: (Ord v, Unify t) => Term t v -> Term t v -> Maybe(Substitution t v)
unify = Term.unify
unify' w s = let s' = variant s w in unify w s'

applySubst (Subst s) = assert (not infinite) $ Term.applySubst (Subst s)
  where infinite = or [ v `elem` vars t | (v,t) <- Map.toList s]