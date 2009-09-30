{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}

module Narradar.Constraints.UsableRules where

import Control.Exception
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import Data.Term
import Data.Term.Rules
import Narradar.Constraints.ICap
import MuTerm.Framework.Problem

class IUsableRules t v thing | thing -> t v where
    iUsableRulesM   :: MonadFresh v m => thing -> [Term t v] -> m thing
    iUsableRulesVar :: thing -> v -> Set (Rule t v)

iUsableRules :: ( term ~ Term t v
                , p    ~ Problem typ
                , Ord term, Enum v
                , IsDPProblem typ, Traversable p, IUsableRules t v (p trs)
                , IsTRS t v trs, GetVars v trs
                ) =>
                p trs -> [term] -> p trs
iUsableRules p tt = runIcap p $ iUsableRulesM p tt



instance (IsDPProblem typ, IsTRS t v trs, IUsableRules t v (typ,trs)) => IUsableRules t v (Problem typ trs)
    where
      iUsableRulesM p tt = do
            (_, trs') <- iUsableRulesM (getProblemType p, getR p) tt
            return $ setR (tRS $ rules trs') p
      iUsableRulesVar p = iUsableRulesVar (getProblemType p, getR p)

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
