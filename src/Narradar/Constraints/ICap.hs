{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.ICap where

import Control.Exception
import Control.Monad.State
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Data.Term hiding (unifies)
import Data.Term.Rules

import Narradar.Constraints.Unify
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Framework

-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, it does just to make GHC happy (avoid recursive module dependencies)

ren :: (Enum v, Traversable t, MonadFresh v m) => Term t v -> m(Term t v)
ren = foldTermM (\_ -> return `liftM` freshVar) (return . Impure)

-- | Use unification instead of just checking if it is a defined symbol
-- This is the icap defined in Rene Thiemann, i.e. it does integrate the REN function
class ICap t v problem | problem -> t v where
    icap :: MonadFresh v m => problem -> Term t v -> m (Term t v)

-- Default instance for unrestricted rewriting
instance (Ord v, Unify t) => ICap t v [Rule t v] where
  icap trs t = do
#ifdef DEBUG
    when (not $ Set.null (getVars trs `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` trs
#else
    assert (Set.null (getVars trs `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules trs)
    let go t = if any (unifies (Impure t) . lhs) rr
                then return `liftM` freshVar else return (Impure t)
        doVar v = return `liftM` freshVar
    foldTermM doVar go t


instance (IsDPProblem typ, ICap t v (typ, trs, trs)) => ICap t v (Problem typ trs) where
  icap p t = icap (getProblemType p, getR p, getP p) t

instance (IsDPProblem typ, ICap t v (typ, trs)) => ICap t v (typ, trs, trs) where
  icap (typ, trs, _dps) t = icap (typ, trs) t


runIcap :: (Enum v, GetVars v thing) => thing -> State (Substitution t (Either v v), [v]) a -> a
runIcap t m = evalState m (emptySubst, freshVars) where
    freshVars = map toEnum [1+maximum (0 : map fromEnum (Set.toList $ getVars t)).. ]

liftIcap (typ,trs) = icap (getBaseFramework typ,trs)