{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.UsableRules where

import Control.Exception
import Control.Monad
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Data.Term
import Data.Term.Rules

import Narradar.Constraints.ICap
import Narradar.Types.Term
import Narradar.Types.Var
import MuTerm.Framework.Problem

class IUsableRules t v thing | thing -> t v where
    iUsableRulesM   :: MonadFresh v m => thing -> [Term t v] -> m thing
    iUsableRulesVarM :: MonadFresh v m => thing -> v -> m(Set (Rule t v))

iUsableRules :: ( p ~ Problem typ
                , Ord (Term t v), Enum v
                , IsDPProblem typ, Traversable p, IUsableRules t v (p trs)
                , IsTRS t v trs, GetVars v trs
                ) =>
                p trs -> [Term t v] -> p trs
iUsableRules p tt = runIcap p $ iUsableRulesM p tt

iUsableRulesVar :: ( p ~ Problem typ
                , Ord (Term t v), Enum v
                , IsDPProblem typ, Traversable p, IUsableRules t v (p trs)
                , IsTRS t v trs, GetVars v trs
                ) =>
                p trs -> v -> Set(Rule t v)
iUsableRulesVar p v = runIcap p $ iUsableRulesVarM p v

class IUsableRules (TermF id) Var thing => NUsableRules id thing | thing -> id
instance IUsableRules (TermF id) Var thing => NUsableRules id thing

instance (IsTRS t v trs, IUsableRules t v (typ, trs)) => IUsableRules t v (typ, trs, trs)
    where
      iUsableRulesM (typ, trs, _dps) tt = do
            (typ', trs') <- iUsableRulesM (typ,trs) tt
            return (typ', trs', _dps)
      iUsableRulesVarM (typ, trs, _dps) = iUsableRulesVarM (typ, trs)

instance (MkDPProblem typ trs, IsTRS t v trs, IUsableRules t v (typ,trs,trs)) => IUsableRules t v (Problem typ trs)
    where
      iUsableRulesM p tt = do
            (_, trs', _dps) <- iUsableRulesM (getProblemType p, getR p, getP p) tt
            return $ setR (tRS $ rules trs') p
      iUsableRulesVarM p = iUsableRulesVarM (getProblemType p, getR p, getP p)

{-
iUsableRules_correct trs (Just pi) = F.toList . go mempty where
  pi_trs = AF.apply pi trs
  --go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t:rest) = evalTerm (\_ -> go acc rest) f t where
    f t0
      | t@(Impure in_t) <- AF.apply pi t0
      , rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , wrap(runSupply' (icap pi_trs `T.mapM` in_t) ids) `unifies` lhs pi_r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])
  ids = [0..] \\ (concatMap.concatMap) collectVars (rules trs)
-}
