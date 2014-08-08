{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.ICap where

import Control.Exception
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Variant
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Data.Term as Family hiding (unifies, Rule)
import Data.Term.Rules

import Narradar.Constraints.Unify
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Framework

import Debug.Hoed.Observe

-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, it does just to make GHC happy (avoid recursive module dependencies)

ren :: (Enum v, Traversable t, Family.Var m ~ v, MonadVariant m) => Term t v -> m(Term t v)
ren = foldTermM (\v -> return `liftM` renaming v) (return . Impure)

-- | Use unification instead of just checking if it is a defined symbol
-- This is the icap defined in Rene Thiemann, i.e. it does integrate the REN function
class ICap problem where
    icapO ::( Rename v
            , Family.Var problem ~ v
            , Family.TermF problem ~ t
            , Family.Var m ~ v
            , MonadVariant m
            , Observable1 m
            , Observable1 t
            ) => Observer -> problem -> [Term t v] -> Term t v -> m (Term t v)
    icap :: ( Rename v
            , Family.Var problem ~ v
            , Family.TermF problem ~ t
            , Family.Var m ~ v
            , MonadVariant m
            , Observable1 m
            , Observable1 t
            ) => problem -> [Term t v] -> Term t v -> m (Term t v)

    icap = icapO nilObserver
    icapO _ = icap

-- Default instance for unrestricted rewriting
instance (Ord v, Rename v, Unify t, Observable(Term t v), Observable v) => ICap [Rule t v] where
  icapO (O o oo) trs s t = do
#ifdef DEBUG
    when (not $ Set.null (getVars trs `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` trs
#else
    assert (Set.null (getVars trs `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules trs)
    let go t = if any (unifies (wrap t) . lhs) rr
                then return `liftM` freshVar else return (wrap t)
        doVar v = return `liftM` renaming v
    foldTermM doVar go t


-- Dodgy ....
type instance Family.TermF (typ, trs, trs) = Family.TermF trs
type instance Family.Var (typ, trs, trs) = Family.Var trs
type instance Family.TermF (typ, trs) = Family.TermF trs
type instance Family.Var (typ, trs) = Family.Var trs

--instance (IsDPProblem typ, ICap (typ, trs, trs)) => ICap (Problem typ trs) where icapO o p t = icapO o (getFramework p, getR p, getP p) t
instance (IsDPProblem typ, ICap (typ, trs)) => ICap (typ, trs, trs) where icapO o (typ, trs, _dps) t = icapO o (typ, trs) t


--runIcap :: (Enum v, Ord v, v ~ Family.Var thing, GetVars thing) => thing -> State (Substitution t (Either v v), [v]) a -> a
runIcap t m = runVariant' freshVars m where
    freshVars = map toEnum [1+maximum (0 : map fromEnum (Set.toList $ getVars t)).. ]

liftIcapO o p = icapO o (getBaseProblem p)
