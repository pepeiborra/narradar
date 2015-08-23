{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.UsableRules where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Free.Extras
import Data.Foldable as F (toList,foldMap)
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable as T (Traversable, mapM)

import Data.Term hiding (Var)
import qualified Data.Term as Family
import qualified Data.Rule.Family as Family
import Data.Term.Rules

import Narradar.Constraints.ICap
import Narradar.Framework
import Narradar.Types.Term

import Debug.Hoed.Observe

class ICap problem => IUsableRules problem where
    iUsableRulesM    :: ( v ~ Family.Var m
                        , v ~ Family.Var problem
                        , t ~ Family.TermF problem
                        , MonadVariant m
                        , Observable1 m
                        ) => problem -> [Term t v] -> [Term t v] -> m problem
    iUsableRulesVarM :: ( v ~ Family.Var m
                        , v ~ Family.Var problem
                        , t ~ Family.TermF problem
                        , MonadVariant m
                        , Observable1 m
                        ) => problem -> [Term t v] -> v -> m problem
    iUsableRulesMO    :: ( v ~ Family.Var m
                        , v ~ Family.Var problem
                        , t ~ Family.TermF problem
                        , MonadVariant m
                        , Observable1 m
                        ) => Observer -> problem -> [Term t v] -> [Term t v] -> m problem
    iUsableRulesVarMO :: ( v ~ Family.Var m
                        , v ~ Family.Var problem
                        , t ~ Family.TermF problem
                        , MonadVariant m
                        , Observable1 m
                        ) => Observer -> problem -> [Term t v] -> v -> m problem
    iUsableRulesM = iUsableRulesMO nilObserver
    iUsableRulesVarM = iUsableRulesVarMO nilObserver
    iUsableRulesMO _ = iUsableRulesM
    iUsableRulesVarMO _ = iUsableRulesVarM

iUsableRules :: ( v ~ Family.Var trs
                , t ~ Family.TermF trs
                , Rule t v ~ Family.Rule trs
                , Ord (Term t v), Enum v, Rename v, Ord v
                , MkProblem typ trs, IsDPProblem typ
                , IsTRS trs, GetVars trs, Monoid trs
                , IUsableRules (Problem typ trs)
                , Traversable (Problem typ)
                , Observable(Term t v)
                , Observable trs
                , Observable typ
                , Observable1 (Problem typ)
                ) =>
                Problem typ trs -> Problem typ trs
iUsableRules p = runIcap p (iUsableRulesMp p)


iUsableRulesO :: ( v ~ Family.Var trs
                , t ~ Family.TermF trs
                , Rule t v ~ Family.Rule trs
                , Ord (Term t v), Enum v, Rename v, Ord v
                , MkProblem typ trs, IsDPProblem typ
                , IsTRS trs, GetVars trs, Monoid trs
                , IUsableRules (Problem typ trs)
                , Traversable (Problem typ)
                , Observable(Term t v)
                , Observable trs
                , Observable typ
                , Observable1 (Problem typ)
                ) =>
                Observer -> Problem typ trs -> Problem typ trs
iUsableRulesO (O o oo) p = runIcap p (oo "iUsableRulesMpO" iUsableRulesMpO p)

iUsableRules' p s tt = runIcap p $ iUsableRulesM p s tt

iUsableRulesVar :: ( v ~ Family.Var trs
                   , t ~ Family.TermF trs
                   , Ord (Term t v), Enum v, Rename v, Ord v
                   , IsDPProblem typ
                   , IsTRS trs, GetVars trs
                   , IUsableRules (Problem typ trs)
                   , Traversable (Problem typ)
                   , Observable (Term t v)
                ) =>
                Problem typ trs -> [Term t v] -> v -> Problem typ trs
iUsableRulesVar p s = runIcap p . iUsableRulesVarMp p s

iUsableRulesMpO :: ( MkProblem typ trs,
                    IsDPProblem typ,
                    IUsableRules (Problem typ trs),
                    MonadVariant m,
                    v ~ Family.Var m,
                    v ~ Family.Var trs,
                    t ~ Family.TermF trs,
                    Rule t v ~ Family.Rule trs,
                    HasRules trs,
                    Monoid trs,
                    Observable1 m,
                    Observable (Term t v),
                    Observable (m trs),
                    Observable trs,
                    Observable typ,
                    Observable1 (Problem typ)
                  ) =>
  Observer -> Problem typ trs -> m (Problem typ trs)

iUsableRulesMpO (O o oo) p = do
  p' <- forM (rules $ getP p) $ \(s :-> t) ->
              oo "iUsableRulesMO" iUsableRulesMO p [s] [t]
  return $ setR (foldMap getR p') p


iUsableRulesMp :: ( MkProblem typ trs,
                    IsDPProblem typ,
                    IUsableRules (Problem typ trs),
                    MonadVariant m,
                    v ~ Family.Var m,
                    v ~ Family.Var trs,
                    t ~ Family.TermF trs,
                    Rule t v ~ Family.Rule trs,
                    HasRules trs,
                    Monoid trs,
                    Observable1 m,
                    Observable (Term t v),
                    Observable (m trs),
                    Observable trs,
                    Observable typ,
                    Observable1 (Problem typ)
                  ) =>
  Problem typ trs -> m (Problem typ trs)

iUsableRulesMp p = iUsableRulesMpO nilObserver p

iUsableRulesVarMp p s = iUsableRulesVarM p s


liftUsableRulesM    p s tt = do
  p' <- iUsableRulesM (getBaseProblem p) s tt
  return (setR (getR p') p)
liftUsableRulesVarM p s v = do
  p' <- iUsableRulesVarM (getBaseProblem p) s v
  return (setR (getR p') p)
-- ----------------------
-- Implementations
-- ----------------

f_UsableRules :: forall typ vk t v trs m.
                 ( Ord (Term t v), Unify t, Ord v, Enum v
                 , Term t v ~ TermFor trs
                 , Family.Rule trs ~ RuleFor trs
                 , v        ~ Family.Var m
                 , vk       ~ ([Term t v] -> v -> m (Problem typ trs))
                 , MkProblem typ trs, IsTRS trs
                 , ICap (Problem typ trs)
                 , GetVars trs
                 , MonadVariant m
                 , Observable1 m
                 , Observable1 t
                 , Observable v
                 ) =>
                 Problem typ trs -> vk -> [Term t v] -> [Term t v] -> m(Problem typ trs)
f_UsableRules (getR -> trs) _  s tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRules p@(getR -> trs) vk s tt = go mempty tt where
  go acc []       = return$ setR (tRS $ map eqModulo $ F.toList acc) p
  go acc (t:rest) = evalTerm (\v -> vk s v >>= \(Set.fromList.rules.getR -> vacc) ->
                               go (Set.map EqModulo vacc `mappend` acc) rest)
                             tk t
      where
--        tk :: t (Term t v) -> m acc
        tk in_t = do
           t'  <- wrap `liftM` (icap p s `T.mapM` in_t)
           let rr  = [ EqModulo rule
                     | rule@(l:->_r) <- rules trs, not(isVar l), l `unifies` t']
               new = Set.difference (Set.fromList rr) acc
           rhsSubterms <- getFresh ((rhs.eqModulo) <$> F.toList new)
           go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])

-- ----------------
-- Needed Rules
-- ----------------

class NeededRules p where
    neededRulesM :: ( v ~ Family.Var m
                    , Term t v ~ TermFor p
                    , MonadVariant m
                    , Observable1 m
                    ) => p -> [Term t v] -> m p

-- We lift the needed rules automatically
instance ( FrameworkExtension ext
         , NeededRules (Problem base trs)
         , MkProblem (ext base) trs
         , IsProblem base
         ) => NeededRules (Problem (ext base) trs)
  where neededRulesM p tt = do
          p' <- neededRulesM (getBaseProblem p) tt
          return $ setR (getR p') p

neededRules :: (Term t v ~ TermFor p
               ,GetVars p
               ,NeededRules p
               ,Enum v, Ord v, Rename v
               ) =>
                p -> [Term t v] -> p
neededRules p tt = runIcap p $ neededRulesM p tt

