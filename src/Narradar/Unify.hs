module Narradar.Unify where

import Control.Monad
import Data.Maybe (isJust)
import Data.Term hiding (unify, unifies)
--import Data.Term (variant)
import qualified Data.Term as Term

unifies  x y = isJust (unify x y)
unifies' x y = isJust (unify' x y)

unify :: (Ord v, Unify t) => Term t v -> Term t v -> Maybe(Substitution t v)
unify = Term.unify
unify' w s = let s' = variant s w in unify w s'
