{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
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
import Narradar.Types.Problem.Infinitary
import Narradar.Framework.Ppr

import Prelude hiding (pi)

type NarrowingGoal  id = NarrowingGoalGen id Rewriting
type CNarrowingGoal id = NarrowingGoalGen id IRewriting

data NarrowingGoalGen id p = NarrowingGoal {pi_PType :: AF_ id, baseProblemType :: p} deriving (Eq, Ord, Show)
instance (Ord id, IsDPProblem p, Functor (DPProblem p)) => IsDPProblem (NarrowingGoalGen id p) where
  data DPProblem (NarrowingGoalGen id p) a = NarrowingGoalProblem {pi::AF_ id, baseProblem::DPProblem p a}
  getProblemType (NarrowingGoalProblem af p) = NarrowingGoal af (getProblemType p)
  mkDPProblem     (NarrowingGoal af p) = (NarrowingGoalProblem af .) . mkDPProblem p
  getP   (NarrowingGoalProblem _  p) = getP p
  getR   (NarrowingGoalProblem _  p) = getR p
  mapR f (NarrowingGoalProblem af p) = NarrowingGoalProblem af (mapR f p)
  mapP f (NarrowingGoalProblem af p) = NarrowingGoalProblem af (mapP f p)

narrowingGoal        g = NarrowingGoal (mkGoalAF g) Rewriting
cnarrowingGoal       g = NarrowingGoal (mkGoalAF g) IRewriting
narrowingGoalProblem g p = NarrowingGoalProblem (g `mappend` AF.init p) p

deriving instance (Eq id, Eq (DPProblem p trs)) => Eq (DPProblem (NarrowingGoalGen id p) trs)
deriving instance (Ord id, Ord (DPProblem p trs)) => Ord (DPProblem (NarrowingGoalGen id p) trs)
deriving instance (Show id, Show (DPProblem p trs)) => Show (DPProblem (NarrowingGoalGen id p) trs)

instance Functor (DPProblem p) => Functor (DPProblem (NarrowingGoalGen id p)) where fmap f (NarrowingGoalProblem af p) = NarrowingGoalProblem af (fmap f p)
instance Foldable (DPProblem p) => Foldable (DPProblem (NarrowingGoalGen id p)) where foldMap f (NarrowingGoalProblem af p) = foldMap f p
instance Traversable (DPProblem p) => Traversable (DPProblem (NarrowingGoalGen id p)) where traverse f (NarrowingGoalProblem af p) = NarrowingGoalProblem af <$> traverse f p

$(derive makeFunctor     ''NarrowingGoalGen)
$(derive makeFoldable    ''NarrowingGoalGen)
$(derive makeTraversable ''NarrowingGoalGen)


instance Ppr p => Ppr (NarrowingGoalGen id p) where
    ppr NarrowingGoal{..} = text "NarrowingGoal" <+> ppr baseProblemType

instance HTMLClass (NarrowingGoalGen id Rewriting) where htmlClass _ = theclass "IRew"
instance HTMLClass (NarrowingGoalGen id IRewriting) where htmlClass _ = theclass "INarr"

instance (Ord id, Ppr (Identifier id), MkNarradarProblem p id) =>
    MkNarradarProblem (NarrowingGoalGen id p) id
 where
   type Typ' (NarrowingGoalGen id p) id = NarrowingGoalGen (Identifier id) (Typ' p id)
   mkNarradarProblem (NarrowingGoal pi typ) trs = narrowingGoalProblem (AF.extendToTupleSymbols pi) p where
      p   = mkNarradarProblem typ trs

instance (Ord id, Ppr (Identifier id), MkNarradarProblem p id) =>
    MkNarradarProblem (NarrowingGoalGen (Identifier id) p) id
 where
   type Typ' (NarrowingGoalGen (Identifier id) p) id = NarrowingGoalGen (Identifier id) (Typ' p id)
   mkNarradarProblem (NarrowingGoal pi typ) trs = narrowingGoalProblem pi p where
      p   = mkNarradarProblem typ trs

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (NarrowingGoalGen id p, trs)
  where
    icap (NarrowingGoal{..},trs) = icap (baseProblemType,trs)


instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v) id, ApplyAF trs id
         ,IUsableRules t v (p,trs), ICap t v (p,trs)) =>
   IUsableRules t v (NarrowingGoalGen id p, trs)
 where
   iUsableRulesM p@(typ@NarrowingGoal{..}, trs) tt = do
      pi_tt <- getFresh (AF.apply pi_PType tt)
      trs'  <- f_UsableRulesAF (baseProblemType, trs) pi_PType (iUsableRulesVar p) pi_tt
      return (typ, tRS $ rules trs')

   iUsableRulesVar (NarrowingGoal{..},trs) = iUsableRulesVar (baseProblemType, trs)