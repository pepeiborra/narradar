{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.ICap where

import Control.Exception
import Control.Monad.State
import Control.Monad.Variant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Data.Term as Family hiding (unifies)
import Data.Term.Rules

import Narradar.Constraints.Unify
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Framework

-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, it does just to make GHC happy (avoid recursive module dependencies)

ren :: (Enum v, Traversable t, VarM m ~ v, MonadVariant m) => Term t v -> m(Term t v)
ren = foldTermM (\v -> return `liftM` renaming v) (return . Impure)

-- | Use unification instead of just checking if it is a defined symbol
-- This is the icap defined in Rene Thiemann, i.e. it does integrate the REN function
class ICap problem where
    icap :: (Rename v, Family.Var problem ~ v, Family.TermF problem ~ t, VarM m ~ v, MonadVariant m) => problem -> Term t v -> m (Term t v)

-- Default instance for unrestricted rewriting
instance (Ord v, Rename v, Unify t) => ICap [Rule t v] where
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
        doVar v = return `liftM` renaming v
    foldTermM doVar go t


-- Dodgy ....
type instance Family.TermF (typ, trs, trs) = Family.TermF trs
type instance Family.Var (typ, trs, trs) = Family.Var trs
type instance Family.TermF (typ, trs) = Family.TermF trs
type instance Family.Var (typ, trs) = Family.Var trs

instance (IsDPProblem typ, ICap (typ, trs, trs)) => ICap (Problem typ trs) where icap p t = icap (getFramework p, getR p, getP p) t
instance (IsDPProblem typ, ICap (typ, trs)) => ICap (typ, trs, trs) where icap (typ, trs, _dps) t = icap (typ, trs) t


--runIcap :: (Enum v, Ord v, v ~ Family.Var thing, GetVars thing) => thing -> State (Substitution t (Either v v), [v]) a -> a
runIcap t m = runVariant' freshVars m where
    freshVars = map toEnum [1+maximum (0 : map fromEnum (Set.toList $ getVars t)).. ]

liftIcap (typ,trs) = icap (getBaseFramework typ,trs)
