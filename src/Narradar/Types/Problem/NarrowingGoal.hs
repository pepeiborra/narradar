{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types.Problem.NarrowingGoal where

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

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Term
import Narradar.Framework.Ppr

import Prelude hiding (pi)

type NarrowingGoal  id = MkNarrowingGoal id Rewriting
type CNarrowingGoal id = MkNarrowingGoal id IRewriting
instance GetPairs (NarrowingGoal id) where getPairs _ = getNPairs

data MkNarrowingGoal id p = NarrowingGoal {pi_PType :: AF_ id, baseProblemType :: p} deriving (Eq, Ord, Show)

instance (Ord id, IsProblem p) => IsProblem (MkNarrowingGoal id p) where
  data Problem (MkNarrowingGoal id p) trs = NarrowingGoalProblem {pi::AF_ id, baseProblem::Problem p trs}
  getProblemType (NarrowingGoalProblem af p) = NarrowingGoal af (getProblemType p)
  getR   (NarrowingGoalProblem _  p) = getR p
  mapR f (NarrowingGoalProblem af p) = NarrowingGoalProblem af (mapR f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (MkNarrowingGoal id p) where
  getP   (NarrowingGoalProblem _  p) = getP p
  mapP f (NarrowingGoalProblem af p) = NarrowingGoalProblem af (mapP f p)

instance (HasSignature trs, id ~ SignatureId trs, Ord id, MkDPProblem p trs) => MkDPProblem (MkNarrowingGoal id p) trs where
  mkDPProblem (NarrowingGoal pi typ) = (narrowingGoalProblem pi.) . mkDPProblem typ

narrowingGoal        g = NarrowingGoal (mkGoalAF g) Rewriting
cnarrowingGoal       g = NarrowingGoal (mkGoalAF g) IRewriting
narrowingGoalProblem g p = NarrowingGoalProblem (g `mappend` AF.init p) p

deriving instance (Eq id, Eq (Problem p trs)) => Eq (Problem (MkNarrowingGoal id p) trs)
deriving instance (Ord id, Ord (Problem p trs)) => Ord (Problem (MkNarrowingGoal id p) trs)
deriving instance (Show id, Show (Problem p trs)) => Show (Problem (MkNarrowingGoal id p) trs)

-- Functor

instance Functor (Problem p) => Functor (Problem (MkNarrowingGoal id p)) where fmap f (NarrowingGoalProblem af p) = NarrowingGoalProblem af (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowingGoal id p)) where foldMap f (NarrowingGoalProblem af p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowingGoal id p)) where traverse f (NarrowingGoalProblem af p) = NarrowingGoalProblem af <$> traverse f p

$(derive makeFunctor     ''MkNarrowingGoal)
$(derive makeFoldable    ''MkNarrowingGoal)
$(derive makeTraversable ''MkNarrowingGoal)

-- Output

instance Pretty p => Pretty (MkNarrowingGoal id p) where
    pPrint NarrowingGoal{..} = text "NarrowingGoal" <+> pPrint baseProblemType

instance HTMLClass (MkNarrowingGoal id Rewriting) where htmlClass _ = theclass "IRew"
instance HTMLClass (MkNarrowingGoal id IRewriting) where htmlClass _ = theclass "INarr"

-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (MkNarrowingGoal id p, trs)
  where
    icap (NarrowingGoal{..},trs) = icap (baseProblemType,trs)

-- Usable Rules

instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v), ApplyAF trs
         ,id ~ AFId trs, AFId (Term t v) ~ id, Ord id
         ,IUsableRules t v (p,trs), ICap t v (p,trs)) =>
   IUsableRules t v (MkNarrowingGoal id p, trs)
 where
   iUsableRulesM p@(typ@NarrowingGoal{..}, trs) tt = do
      pi_tt <- getFresh (AF.apply pi_PType tt)
      trs'  <- f_UsableRulesAF (baseProblemType, trs) pi_PType (iUsableRulesVar p) pi_tt
      return (typ, tRS $ rules trs')

   iUsableRulesVar (NarrowingGoal{..},trs) = iUsableRulesVar (baseProblemType, trs)