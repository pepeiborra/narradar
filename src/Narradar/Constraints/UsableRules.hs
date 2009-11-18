{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.UsableRules where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Foldable as F (toList)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable as T (Traversable, mapM)

import Data.Term
import Data.Term.Rules

import Narradar.Constraints.ICap
import Narradar.Framework
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Types.ArgumentFiltering as AF (AF_, ApplyAF(..))

class Monoid trs => IUsableRules t v typ trs | trs -> t v where
    iUsableRulesM    :: MonadFresh v m => typ -> trs -> trs -> [Term t v] -> m trs
    iUsableRulesVarM :: MonadFresh v m => typ -> trs -> trs -> v -> m(Set (Rule t v))
    iUsableRulesM  typ trs _dps = iUsableRules2M typ trs

data Proxy a
proxy = undefined

deriveUsableRulesFromTRS :: forall t v typ trs m.
                            (IUsableRules t v typ trs, IsTRS t v trs, MonadFresh v m) =>
                            Proxy trs -> typ -> [Rule t v] -> [Rule t v] -> [Term t v] -> m [Rule t v]
deriveUsableRulesFromTRS _   typ r p = liftM rules . iUsableRulesM typ (tRS r :: trs) (tRS p :: trs)

deriveUsableRulesVarFromTRS :: forall t v typ trs m.
                              (IUsableRules t v typ trs, IsTRS t v trs, MonadFresh v m) =>
                            Proxy trs -> typ -> [Rule t v] -> [Rule t v] -> v -> m (Set(Rule t v))
deriveUsableRulesVarFromTRS _ typ r p = iUsableRulesVarM typ (tRS r :: trs) (tRS p :: trs)

iUsableRules2M typ trs = iUsableRulesM typ trs mempty
iUsableRulesVar2M typ trs = iUsableRulesVarM typ trs mempty

iUsableRules :: ( p ~ Problem typ
                , Ord (Term t v), Enum v
                , MkProblem typ trs, IsDPProblem typ, Traversable p
                , IsTRS t v trs, GetVars v trs, IUsableRules t v typ trs
                ) =>
                p trs -> [Term t v] -> p trs
iUsableRules p = runIcap p . iUsableRulesMp p

iUsableRulesVar :: ( p ~ Problem typ
                , Ord (Term t v), Enum v
                , IsDPProblem typ, Traversable p
                , IsTRS t v trs, GetVars v trs, IUsableRules t v typ trs
                ) =>
                p trs -> v -> Set(Rule t v)
iUsableRulesVar p = runIcap p . iUsableRulesVarMp p

iUsableRulesMp ::
  (MkProblem typ trs,
   IsDPProblem typ,
   IUsableRules t v typ trs,
   MonadFresh v m) =>
  Problem typ trs -> [Data.Term.Term t v] -> m (Problem typ trs)

iUsableRulesMp p tt = do { trs' <- iUsableRulesM (getProblemType p) (getR p) (getP p) tt
                         ; return $ setR trs' p}

iUsableRulesVarMp p = iUsableRulesVarM (getProblemType p) (getR p) (getP p)


liftUsableRulesM    typ trs dps = iUsableRulesM (getBaseFramework typ) trs dps
liftUsableRulesVarM typ trs dps = iUsableRulesVarM (getBaseFramework typ) trs dps

-- ----------------------
-- Implementations
-- ----------------

f_UsableRules :: forall term vk acc t v trs typ problem m.
                 ( Ord (Term t v), Unify t, Ord v
                 , problem ~ (typ, trs)
                 , term ~ Term t v
                 , vk ~ (v -> m acc)
                 , acc ~ Set (Rule t v)
                 , HasRules t v trs, GetVars v trs
                 , ICap t v problem
                 , MonadFresh v m
                 ) =>
                 problem -> vk -> [term] -> m acc
f_UsableRules p@(_,trs) _  tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRules p@(_,trs) vk tt = go mempty tt where
  go acc []       = return acc
  go acc (t:rest) = evalTerm (\v -> vk v >>= \vacc -> go (vacc `mappend` acc) rest) tk t where
        tk :: t (Term t v) -> m acc
        tk in_t = do
           t'  <- wrap `liftM` (icap p `T.mapM` in_t)
           let rr  = [ rule | rule@(l:->r) <- rules trs, not(isVar l), l `unifies` t']
               new = Set.difference (Set.fromList rr) acc
           rhsSubterms <- getFresh (rhs <$> F.toList new)
           go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])


f_UsableRulesAF :: forall term vk acc t id v trs typ problem m.
                 ( problem ~ (typ,trs)
                 , term    ~ Term t v
                 , vk      ~ (v -> m acc)
                 , acc     ~ Set (Rule t v)
                 , id      ~ AFId trs, AFId term ~ id, Ord id
                 , Ord (Term t v), Unify t, Ord v, ApplyAF term
                 , HasRules t v trs, ApplyAF trs, GetVars v trs
                 , ICap t v problem
                 , MonadFresh v m
                 ) =>
                 problem -> AF_ id -> vk -> [term] -> m acc

f_UsableRulesAF p@(typ,trs)    _   _ tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRulesAF p@(typ,trs) pi vk tt = go mempty tt where
    pi_rules = [(AF.apply pi r, r) | r <- rules trs]
    pi_trs   = AF.apply pi trs
  --go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
    go acc []       = return acc
    go acc (t:rest) = evalTerm (\v -> vk v >>= \vacc -> go (vacc `mappend` acc) rest) tk t where
     tk in_t = do
        t' <- wrap `liftM` (icap (typ, pi_trs) `T.mapM` in_t)
        let rr = Set.fromList
                [rule | (l:->r, rule) <- pi_rules, not (isVar l), t' `unifies` l]
            new = Set.difference rr acc
        rhsSubterms <- getFresh (AF.apply pi . rhs <$> F.toList new)
        go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])