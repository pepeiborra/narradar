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

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Framework
import Narradar.Framework.Ppr

import Prelude hiding (pi)

type NarrowingGoal  id = MkNarrowingGoal id Rewriting
type CNarrowingGoal id = MkNarrowingGoal id IRewriting
instance GetPairs (NarrowingGoal id) where getPairs _ = getNPairs

data MkNarrowingGoal id p = NarrowingGoal (Goal id) (AF_ id) p
  deriving (Eq, Ord, Show)

instance (Ord id, IsProblem p) => IsProblem (MkNarrowingGoal id p) where
  data Problem (MkNarrowingGoal id p) trs = NarrowingGoalProblem {goal::Goal id, pi::AF_ id, baseProblem::Problem p trs}
  getProblemType (NarrowingGoalProblem g af p) = NarrowingGoal g af (getProblemType p)
  getR   (NarrowingGoalProblem _ _  p) = getR p

instance (Ord id, MkProblem p trs) => MkProblem (MkNarrowingGoal id p) trs where
  mkProblem (NarrowingGoal g af p) rr = NarrowingGoalProblem g af (mkProblem p rr)
  mapR f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (mapR f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (MkNarrowingGoal id p) where
  getP   (NarrowingGoalProblem _ _  p) = getP p

instance (HasSignature trs, id ~ SignatureId trs, Ord id, MkDPProblem p trs) =>
    MkDPProblem (MkNarrowingGoal id p) trs
 where
  mkDPProblem (NarrowingGoal g pi typ) = (narrowingGoalProblem g pi.) . mkDPProblem typ
  mapP f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (mapP f p)


instance FrameworkExtension (MkNarrowingGoal id) where
  getBaseFramework (NarrowingGoal _ _ p) = p
  getBaseProblem = baseProblem
  setBaseProblem p0 p = p{baseProblem = p0}

narrowingGoal        g = NarrowingGoal g (mkGoalAF g) rewriting
cnarrowingGoal       g = NarrowingGoal g (mkGoalAF g) irewriting

narrowingGoalProblem g pi p = NarrowingGoalProblem g (pi `mappend` AF.init p) p

deriving instance (Eq id, Eq (Problem p trs)) => Eq (Problem (MkNarrowingGoal id p) trs)
deriving instance (Ord id, Ord (Problem p trs)) => Ord (Problem (MkNarrowingGoal id p) trs)
deriving instance (Show id, Show (Problem p trs)) => Show (Problem (MkNarrowingGoal id p) trs)

-- Functor

instance Functor (Problem p) => Functor (Problem (MkNarrowingGoal id p)) where fmap f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowingGoal id p)) where foldMap f (NarrowingGoalProblem _ _ p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowingGoal id p)) where traverse f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af <$> traverse f p

$(derive makeFunctor     ''MkNarrowingGoal)
$(derive makeFoldable    ''MkNarrowingGoal)
$(derive makeTraversable ''MkNarrowingGoal)

-- Data.Term instances


-- Output

instance Pretty p => Pretty (MkNarrowingGoal id p) where
    pPrint (NarrowingGoal _ _ p) = text "NarrowingGoal" <+> pPrint p

instance HTMLClass (MkNarrowingGoal id Rewriting) where htmlClass _ = theclass "IRew"
instance HTMLClass (MkNarrowingGoal id IRewriting) where htmlClass _ = theclass "INarr"


-- ICap

instance ICap t v (base, NarradarTRS t v) => ICap t v (MkNarrowingGoal id base, NarradarTRS t v) where icap = liftIcap

-- Usable Rules

instance (IUsableRules t v base trs) =>
  IUsableRules t v (MkNarrowingGoal id base) trs where
   iUsableRulesM    = liftUsableRulesM
   iUsableRulesVarM = liftUsableRulesVarM

{-
-- Insert Pairs

instance (Pretty id, Ord id, MkDPProblem b (NTRS id)) =>InsertDPairs (NarrowingGoal id) (NTRS id) where
    insertDPairs = insertDPairsDefault
-}