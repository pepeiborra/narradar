{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
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
import Data.Foldable as F (toList)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable as T (Traversable, mapM)

import Data.Term hiding (Rule, Var)
import qualified Data.Term as Family
import qualified Data.Rule.Family as Family
import Data.Term.Rules

import Narradar.Constraints.ICap
import Narradar.Framework
import Narradar.Types.Term
import Narradar.Types.ArgumentFiltering as AF (AF_, ApplyAF(..))
import Narradar.Utils (Proxy)

import Debug.Hoed.Observe

class Monoid trs => IUsableRules typ trs where
    iUsableRulesM    :: ( v ~ Family.Var m
                        , v ~ Family.Var trs
                        , t ~ Family.TermF trs
                        , MonadVariant m
                        , Observable1 m
                        ) => typ -> trs -> trs -> [Term t v] -> [Term t v] -> m trs
    iUsableRulesVarM :: ( v ~ Family.Var m
                        , v ~ Family.Var trs
                        , t ~ Family.TermF trs
                        , MonadVariant m
                        , Observable1 m
                        ) => typ -> trs -> trs -> [Term t v] -> v -> m(Set (Rule t v))

deriveUsableRulesFromTRS :: forall t v typ trs m.
                            ( IUsableRules typ trs, IsTRS trs
                            , v ~ Family.Var m
                            , v ~ Family.Var trs
                            , t ~ Family.TermF trs
                            , Rule t v ~ Family.Rule trs
                            , MonadVariant m
                            , Observable1 m
                            ) =>
                            Proxy trs -> typ -> [Rule t v] -> [Rule t v] -> [Term t v] -> [Term t v] -> m [Rule t v]
deriveUsableRulesFromTRS _ typ r p s = liftM rules . iUsableRulesM typ (tRS r :: trs) (tRS p :: trs) s

deriveUsableRulesVarFromTRS :: forall t v typ trs m.
                              ( IUsableRules typ trs, IsTRS trs
                              , v ~ Family.Var m
                              , v ~ Family.Var trs
                              , t ~ Family.TermF trs
                              , Rule t v ~ Family.Rule trs
                              , MonadVariant m
                              , Observable1 m
                              ) =>
                            Proxy trs -> typ -> [Rule t v] -> [Rule t v] -> [Term t v] -> v -> m (Set(Rule t v))
deriveUsableRulesVarFromTRS _ typ r p s = iUsableRulesVarM typ (tRS r :: trs) (tRS p :: trs) s

iUsableRules :: ( p ~ Problem typ
                , v ~ Family.Var trs
                , t ~ Family.TermF trs
                , Rule t v ~ Family.Rule trs
                , Ord (Term t v), Enum v, Rename v, Ord v
                , MkProblem typ trs, IsDPProblem typ, Traversable p
                , IsTRS trs, GetVars trs, IUsableRules typ trs
                , Observable(Term t v)
                , Observable trs
                , Observable typ
                ) =>
                p trs -> p trs
iUsableRules p = runIcap p (iUsableRulesMp p)

iUsableRules' p s tt = runIcap p $ do
  trs' <- iUsableRulesM (getFramework p) (getR p) (getP p) s tt
  return $ setR trs' p

iUsableRulesVar :: ( p ~ Problem typ
                   , v ~ Family.Var trs
                   , t ~ Family.TermF trs
                   , Ord (Term t v), Enum v, Rename v, Ord v
                   , IsDPProblem typ, Traversable p
                   , IsTRS trs, GetVars trs, IUsableRules typ trs
                   , Observable (Term t v)
                ) =>
                p trs -> [Term t v] -> v -> Set(Rule t v)
iUsableRulesVar p s = runIcap p . iUsableRulesVarMp p s

iUsableRules3 typ trs dps s = runIcap (getVars trs `mappend` getVars dps) . iUsableRulesM typ trs dps s

iUsableRulesMp :: ( MkProblem typ trs,
                    IsDPProblem typ,
                    IUsableRules typ trs,
                    MonadVariant m,
                    v ~ Family.Var m,
                    v ~ Family.Var trs,
                    t ~ Family.TermF trs,
                    Rule t v ~ Family.Rule trs,
                    HasRules trs,
                    Observable1 m,
                    Observable (Term t v),
                    Observable (m trs),
                    Observable trs,
                    Observable typ
                  ) =>
  Problem typ trs -> m (Problem typ trs)

iUsableRulesMp p = do
  trs' <- forM (rules $ getP p) $ \(s :-> t) ->
   {-gdmobserve "usablerules"-} iUsableRulesM (getFramework p) (getR p) (getP p) [s] [t]
  return $ setR (mconcat trs') p


iUsableRulesVarMp p s = iUsableRulesVarM (getFramework p) (getR p) (getP p) s


liftUsableRulesM    typ trs dps = iUsableRulesM (getBaseFramework typ) trs dps
liftUsableRulesVarM typ trs dps = iUsableRulesVarM (getBaseFramework typ) trs dps

-- ----------------------
-- Implementations
-- ----------------

f_UsableRules :: forall term vk t v trs typ problem m.
                 ( Ord (Term t v), Unify t, Ord v, Enum v
                 , term     ~ Term t v
                 , v        ~ Family.Var m
                 , v        ~ Family.Var trs
                 , t        ~ Family.TermF trs
                 , Rule t v ~ Family.Rule trs
                 , vk       ~ ([term] -> v -> m (Set(Rule t v)))
                 , HasRules trs, GetVars trs
                 , ICap (typ,trs)
                 , MonadVariant m
                 , Observable1 m
                 , Observable1 t
                 ) =>
                 (typ, trs) -> vk -> [term] -> [term] -> m (Set(Rule t v))
f_UsableRules (_,trs) _  s tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRules p@(_,trs) vk s tt = go mempty tt where
  go acc []       = return$ Set.map eqModulo acc
  go acc (t:rest) = evalTerm (\v -> vk s v >>= \vacc -> go (Set.map EqModulo vacc `mappend` acc) rest) tk t
      where
--        tk :: t (Term t v) -> m acc
        tk in_t = do
           t'  <- wrap `liftM` (icap p s `T.mapM` in_t)
           let rr  = [ EqModulo rule
                     | rule@(l:->_r) <- rules trs, not(isVar l), l `unifies` t']
               new = Set.difference (Set.fromList rr) acc
           rhsSubterms <- getFresh ((rhs.eqModulo) <$> F.toList new)
           go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])



f_UsableRulesAF :: forall term vk acc t id v trs typ problem m.
                 ( term    ~ Term t v
                 , t       ~ Family.TermF trs
                 , v       ~ Family.Var m
                 , v       ~ Family.Var trs
                 , Rule t v~ Family.Rule trs
                 , vk      ~ ([term] -> v -> m acc)
                 , acc     ~ Set (Rule t v)
                 , id      ~ Id trs
                 , id      ~ Id term
                 , Ord id
                 , Ord (Term t v), Unify t, Ord v, ApplyAF term
                 , HasRules trs, ApplyAF trs, GetVars trs
                 , ICap (typ, trs)
                 , MonadVariant m
                 , Observable1 m
                 , Observable1 t
                 ) =>
                 (typ, trs) -> AF_ id -> vk -> [term] -> [term] -> m acc

f_UsableRulesAF p@(typ,trs)    _   _ s tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRulesAF p@(typ,trs) pi vk s tt = go mempty tt where
    pi_rules = [(AF.apply pi r, r) | r <- rules trs]
    pi_trs   = AF.apply pi trs
  --go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
    go acc []       = return acc
    go acc (t:rest) = evalTerm (\v -> vk s v >>= \vacc -> go (vacc `mappend` acc) rest) tk t where
     tk in_t = do
        t' <- wrap `liftM` (icap (typ, pi_trs) s `T.mapM` in_t)
        let rr = Set.fromList
                [rule | (l:->r, rule) <- pi_rules, not (isVar l), t' `unifies` l]
            new = Set.difference rr acc
        rhsSubterms <- getFresh (AF.apply pi . rhs <$> F.toList new)
        go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])


-- ----------------
-- Needed Rules
-- ----------------

class Monoid trs => NeededRules typ trs where
    neededRulesM :: ( v ~ Family.Var m
                    , t ~ Family.TermF trs
                    , v ~ Family.Var trs
                    , MonadVariant m
                    , Observable1 m
                    ) => typ -> trs -> trs -> [Term t v] -> m trs

-- We lift the needed rules automatically
instance (FrameworkExtension ext, NeededRules base trs) => NeededRules (ext base) trs
  where neededRulesM typ trs dps = neededRulesM (getBaseFramework typ) trs dps


neededRules :: ( p ~ Problem typ
               , v ~ Family.Var trs
               , t ~ Family.TermF trs
               , Ord (Term t v), Enum v, Rename v, Ord v
               , MkProblem typ trs, IsDPProblem typ, Traversable p
               , IsTRS trs, GetVars trs, NeededRules typ trs
               , Observable (Term t v)
               ) =>
                p trs -> [Term t v] -> p trs
neededRules p tt = runIcap p $ do
                     trs' <- neededRulesM (getFramework p) (getR p) (getP p) tt
                     return $ setR trs' p

