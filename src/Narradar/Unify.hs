module Narradar.Unify where

import Control.Monad
import Data.Maybe (isJust)
import TRS hiding (unify, unifies)
import qualified TRS

unifies  x y = isJust (unify x y)
unifies' x y = isJust (unify' x y)

unify :: (MonadPlus m,  Unifyable f) => Term f -> Term f -> m(Subst f)
unify = TRS.unify
unify' w s = let [s'] = variant' [s] [w] in unify w s'
