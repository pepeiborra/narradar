{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types.Problem.Infinitary where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.XHtml (theclass)

import Data.Term
import Data.Term.Rules

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..), PolyHeuristic, MkHeu, mkHeu, bestHeu)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Term
import Narradar.Framework.Ppr

import Prelude hiding (pi)


data Infinitary id p = Infinitary {pi_PType :: AF_ id, baseProblemType :: p} deriving (Eq, Ord, Show)
instance (Ord id, IsProblem p) => IsProblem (Infinitary id p)  where
  data Problem (Infinitary id p) a = InfinitaryProblem {pi::AF_ id, baseProblem::Problem p a}
  getProblemType (InfinitaryProblem af p) = Infinitary af (getProblemType p)
  getR   (InfinitaryProblem _  p) = getR p

instance (Ord id, MkProblem p trs, HasSignature (Problem p trs), id ~ SignatureId (Problem p trs)) =>
    MkProblem (Infinitary id p) trs where
  mkProblem (Infinitary af base) rr = InfinitaryProblem (af `mappend` AF.init p) p where p = mkProblem base rr
  mapR f (InfinitaryProblem af p) = InfinitaryProblem af (mapR f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (Infinitary id p) where
  getP   (InfinitaryProblem _  p) = getP p

instance (id ~ SignatureId (Problem p trs), HasSignature (Problem p trs), Ord id, MkDPProblem p trs) =>
    MkDPProblem (Infinitary id p) trs where
  mapP f (InfinitaryProblem af p) = InfinitaryProblem af (mapP f p)
  mkDPProblem (Infinitary af base) rr dp = InfinitaryProblem (af `mappend` AF.init p) p
    where p = mkDPProblem base rr dp


infinitary        g p = Infinitary (mkGoalAF g) p
infinitaryProblem g p = InfinitaryProblem (g `mappend` AF.init p) p
mkDerivedInfinitaryProblem g mkH p = do
  let heu = mkHeu mkH p
      af  = mkGoalAF g `mappend` AF.init p
  af' <-  Set.toList $ invariantEV heu p af
  let p' = InfinitaryProblem af' $ (iUsableRules p (rhs <$> rules (getP p)))
  return p'

deriving instance (Eq id, Eq (Problem p trs)) => Eq (Problem (Infinitary id p) trs)
deriving instance (Ord id, Ord (Problem p trs)) => Ord (Problem (Infinitary id p) trs)
deriving instance (Show id, Show (Problem p trs)) => Show (Problem (Infinitary id p) trs)

-- Functor

instance Functor (Problem p) => Functor (Problem (Infinitary id p)) where fmap f (InfinitaryProblem af p) = InfinitaryProblem af (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (Infinitary id p)) where foldMap f (InfinitaryProblem af p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (Infinitary id p)) where traverse f (InfinitaryProblem af p) = InfinitaryProblem af <$> traverse f p

$(derive makeFunctor     ''Infinitary)
$(derive makeFoldable    ''Infinitary)
$(derive makeTraversable ''Infinitary)

-- Data.Term instances

-- Output

instance Pretty p => Pretty (Infinitary id p) where
    pPrint Infinitary{..} = text "Infinitary" <+> pPrint baseProblemType

instance HTMLClass (Infinitary id Rewriting) where htmlClass _ = theclass "InfRew"
instance HTMLClass (Infinitary id IRewriting) where htmlClass _ = theclass "InfIRew"
instance HTMLClass (Infinitary id Narrowing) where htmlClass _ = theclass "InfNarr"
instance HTMLClass (Infinitary id CNarrowing) where htmlClass _ = theclass "InfCNarr"

-- Icap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (Infinitary id p, trs)
  where
    icap (Infinitary{..},trs) = icap (baseProblemType,trs)

-- Usable Rules

instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v), ApplyAF trs
         , id ~ AFId trs, AFId (Term t v) ~ id, Ord id
         ,IUsableRules t v (p,trs), ICap t v (p,trs)) =>
   IUsableRules t v (Infinitary id p, trs)
 where
   iUsableRulesM p@(typ@Infinitary{..}, trs) tt = do
      pi_tt <- getFresh (AF.apply pi_PType tt)
      trs'  <- f_UsableRulesAF (baseProblemType, trs) pi_PType (iUsableRulesVarM p) pi_tt
      return (typ, tRS $ rules trs')

   iUsableRulesVarM (Infinitary{..},trs) = iUsableRulesVarM (baseProblemType, trs)

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
                [r | (pi_r, r) <- pi_rules, t' `unifies` lhs pi_r]
            new = Set.difference rr acc
        rhsSubterms <- getFresh (AF.apply pi . rhs <$> F.toList new)
        go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])
