{-# LANGUAGE ScopedTypeVariables, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE Rank2Types, ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Narradar.Constraints.Unify
       ( module Narradar.Framework.Constraints,
         module Narradar.Constraints.Unify,
         module Data.Term,
         module Data.Term.Rules
       ) where

import Control.Arrow
import Control.Exception (assert)
import Control.Monad (liftM)
import Control.Monad.ConstrainedNormal
import Data.Constraint (Dict(..), (:-)(..))
import Data.Foldable (Foldable, toList)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Monoid
import Data.Term (Substitution_(..), GetVars(..), Term, Match(..), Unify(..), EqModulo(..)
                 ,unifies,matches,variant,equiv,vars,zonkSubst)
import Data.Term.Rules hiding (matches', unifies', find)
import Data.Map (Map)
import Data.Traversable (Traversable)
import qualified Data.Map  as Map
import qualified Data.Term as Term
import qualified Data.Term as Family
import Narradar.Framework.Constraints
import Narradar.Framework.Ppr

import Debug.Hoed.Observe

type SubstitutionNF constraint a = NF constraint Substitution_ a
type SubstitutionF a  = SubstitutionNF GetVarsObservable a
type Substitution t v  = SubstitutionF (Term t v)
type SubstitutionFor t = Substitution (Family.TermF t) (Family.Var t)

instance (Eq a, GetVars a, c :=># GetVars, Ord(Family.Var a), Observable(Family.Var a)
         ) => Eq (SubstitutionNF c a) where
  a == b = unSubst(lowerSubst a) == unSubst(lowerSubst b)
instance (Ord a, GetVars a, c :=># GetVars, Ord(Family.Var a), Observable(Family.Var a)
         ) => Ord (SubstitutionNF c a) where
  compare a b = unSubst(lowerSubst a) `compare` unSubst(lowerSubst b)
instance (Ord a, GetVars a, c :=># GetVars, Ord(Family.Var a), Pretty a, Pretty(Family.Var a), Observable(Family.Var a)
         ) => Pretty(SubstitutionNF c a) where
  pPrint = pPrint . lowerSubst

instance (v ~ Family.Var (t v), constraint (t v), constraint :=># GetVars, GetVars(t v)
         , Ord v, Observable v, Monad t
         ) => Monoid (SubstitutionNF constraint (t v)) where
  mempty  = liftNF Term.emptySubst
  mappend a b = liftNF (Term.appendSubst (lowerSubst a) (lowerSubst b))

liftSubstNF :: (GetVarsObservable a) => Substitution_ a -> SubstitutionF a
liftSubstNF = liftNF

lowerSubst :: forall constraint a.
              (constraint :=># GetVars, Ord(Family.Var a), GetVars a, Observable(Family.Var a)
              ) =>
           SubstitutionNF constraint a -> Substitution_ a
lowerSubst = lowerNF (fmapSubst ins) where
  fmapSubst :: forall x. constraint x => constraint x :- GetVars x -> (x -> a) -> Substitution_ x -> Substitution_ a
  fmapSubst (Sub Dict) f (Subst m) = Subst (Map.mapKeys g $ fmap f m) where
      g (toList.getVars.f.fromVar -> [v]) = v
      g _ = error "fmap for SubstitutionF: only homomorphisms on variables can be mapped"

flushSubst :: (GetVars a, Observable a, Observable(Family.Var a), Ord(Family.Var a)
              ) => SubstitutionF a -> SubstitutionF a
flushSubst = liftNF . lowerSubst

applySubst :: (v ~ Family.Var(t v), Ord v, Observable v
              ,Monad t
              ,c :=># GetVars, GetVars (t v)
              ) => SubstitutionNF c (t v) -> t v -> t v
applySubst = Term.applySubst . lowerSubst

fromListSubst ::(v ~ Family.Var a, Ord v, Observable v, Observable a, GetVars a
                ) => [(Family.Var a, a)] -> SubstitutionF a
fromListSubst = liftNF . Term.fromListSubst

runMEnv :: (Ord v, Observable v, Observable1 t
           ,Functor t, Foldable t, Monad m
           ) => Term.MEnvT t v m a -> m (a, Substitution t v)
runMEnv = liftM(second liftNF) . Term.runMEnv

unifies' x y = isJust (unify' x y)
matches' x y = isJust (match' x y)

unify :: (Ord v, Unify t, Observable(Term t v), Observable v) => Term t v -> Term t v -> Maybe(Substitution t v)
unify t u = fmap liftNF (Term.unify t u)
match :: (Ord v, Observable(Term t v), Observable v, Traversable t, Match t) => Term t v -> Term t v -> Maybe(Substitution t v)
match t u = fmap liftNF (Term.match t u)

unify' w s = let s' = variant s w in maybe (fail "unify'") return (unify w s')
match' w s = let s' = variant s w in maybe (fail "match'") return (match w s')
getUnifier' w s = let s' = getVariant s w in maybe (fail "getUnifier'") return (getUnifier w s')


applySubstSafe (lowerSubst -> s) = assert (not infinite) $ Term.applySubst (zonkSubst s)
  where infinite = or [ v `elem` vars t | (v,t) <- Map.toList (unSubst s)]
