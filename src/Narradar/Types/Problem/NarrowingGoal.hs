{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Narradar.Types.Problem.NarrowingGoal where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM, fmapDefault, foldMapDefault)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.XHtml (theclass)

import Data.Term
import qualified Data.Term.Family as Family
import Data.Term.Rules

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..), PolyHeuristic, MkHeu, mkHeu, bestHeu, fromAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Term
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils (chunks)

import Prelude hiding (pi)

import Debug.Hoed.Observe

type NarrowingGoal id = MkNarrowingGoal id Rewriting
type CNarrowingGoal id = MkNarrowingGoal id IRewriting

data MkNarrowingGoal id p = forall heu . PolyHeuristic heu id =>
                          NarrowingGoal (Goal id) (AF_ id) (MkHeu heu) p

--instance (HasSignature p) => HasSignature (MkNarrowingGoal id p) where getSignature (NarrowingGoal _ _ _ p) = getSignature p

instance (Ord id, IsProblem p) => IsProblem (MkNarrowingGoal id p)  where
  data Problem (MkNarrowingGoal id p) a = NarrowingGoalProblem {goal::Goal id, pi::AF_ id, baseProblem::Problem p a}
  getFramework (NarrowingGoalProblem g af p) = NarrowingGoal g af bestHeu (getFramework p)
  getR   (NarrowingGoalProblem _ _ p) = getR p

instance ( Ord id
         , IsDPProblem p, HasSignature (Problem p trs)
         , id ~ Family.Id trs
         , MkProblem p trs
         ) =>
    MkProblem (MkNarrowingGoal id p) trs where
  mkProblem (NarrowingGoal g af _ base) rr
      = NarrowingGoalProblem g (af `mappend` AF.init p) p where p = mkProblem base rr
  mapRO o f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (mapRO o f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (MkNarrowingGoal id p) where
  getP   (NarrowingGoalProblem _ _ p) = getP p

instance ( id ~ Family.Id trs
         , HasSignature(Problem p trs)
         , Ord id
         , MkDPProblem p trs) =>
    MkDPProblem (MkNarrowingGoal id p) trs where
  mapPO o f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (mapPO o f p)
  mkDPProblemO o (NarrowingGoal g af _ base) rr dp = NarrowingGoalProblem g (af `mappend` AF.init p) p
    where p = mkDPProblemO o base rr dp

narrowingGoal  g = narrowingGoal' g (mkGoalAF g)
cnarrowingGoal g = NarrowingGoal g (mkGoalAF g) bestHeu irewriting
narrowingGoal' g af = NarrowingGoal g af bestHeu rewriting

mkDerivedNarrowingGoalProblem g mkH p = do
  let heu = mkHeu mkH p
      af  = mkGoalAF g `mappend` AF.init p
  af' <-  Set.toList $ invariantEV heu (rules p) af
  let p' = NarrowingGoalProblem g af' p --  $ (iUsableRules p (rhs <$> rules (getP p)))
  return p'

-- Eq,Ord,Show
deriving instance (Eq id, Eq (Problem p trs)) => Eq (Problem (MkNarrowingGoal id p) trs)
deriving instance (Ord id, Ord (Problem p trs)) => Ord (Problem (MkNarrowingGoal id p) trs)
deriving instance (Show id, Show (Problem p trs)) => Show (Problem (MkNarrowingGoal id p) trs)

-- Functor
instance Functor (MkNarrowingGoal id) where fmap = fmapDefault
instance Foldable (MkNarrowingGoal id) where foldMap = foldMapDefault
instance Traversable (MkNarrowingGoal id) where traverse f (NarrowingGoal g pi heu p) = NarrowingGoal g pi heu <$> f p

instance Functor (Problem p) => Functor (Problem (MkNarrowingGoal id p)) where fmap f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowingGoal id p)) where foldMap f (NarrowingGoalProblem g af p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowingGoal id p)) where traverse f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af <$> traverse f p

-- Framework

instance FrameworkExtension (MkNarrowingGoal id) where
  getBaseFramework (NarrowingGoal _ _ _ p) = p
  getBaseProblem = baseProblem
  liftProblem   f p = f (baseProblem p) >>= \p0' -> return p{baseProblem = p0'}
  liftFramework f (NarrowingGoal g af heu p) = NarrowingGoal g af heu (f p)
  liftProcessorS = liftProcessorSdefault

instance HasSignature (Problem p trs) => HasSignature (Problem (MkNarrowingGoal id p) trs) where
  getSignature = getSignature . getBaseProblem

-- Output

instance Pretty p => Pretty (MkNarrowingGoal id p) where
    pPrint (NarrowingGoal _ _ _ b) = text "NarrowingGoal" <+> pPrint b

instance HTMLClass (MkNarrowingGoal id Rewriting) where htmlClass _ = theclass "NDP"
instance HTMLClass (MkNarrowingGoal id IRewriting) where htmlClass _ = theclass "GNDP"

instance (HasRules trs, GetVars trs, Pretty v, Pretty (t(Term t v))
         ,Pretty id, Pretty (Goal id)
         ,Foldable t, HasId1 t
         ,id ~ Family.Id t
         ,PprTPDB (Problem base trs), HasMinimality base
         ) => PprTPDB (Problem (MkNarrowingGoal id base) trs) where
  pprTPDB (NarrowingGoalProblem g pi p) =
      pprTPDB (setMinimality A p) $$
      parens (text "STRATEGY NARROWING") $$
      parens (text "STRATEGY GOAL" <+> g)

-- Icap

instance (HasRules trs, Unify (Family.TermF trs), GetVars trs, ICap (Problem p trs)) =>
    ICap (Problem (MkNarrowingGoal id p) trs)
  where
    icapO = liftIcapO

-- Usable Rules

instance ( id ~ Family.Id trs
         , id ~ Family.Id t
         , FrameworkProblem (MkNarrowingGoal id p) trs
         , FrameworkProblem p trs
         ) =>
   IUsableRules (Problem (MkNarrowingGoal id p) trs)
 where
   iUsableRulesM p s tt = return p
   iUsableRulesVarM = liftUsableRulesVarM

instance Observable1 (MkNarrowingGoal id) where observer1 = observeOpaque "narrowingGoal"
instance Observable a => Observable(MkNarrowingGoal id a) where observer = observer1 ; observers = observers1
instance Observable1 (Problem (MkNarrowingGoal id p)) where observer1 = observeOpaque "narrowingGoal problem"
instance Observable a => Observable(Problem(MkNarrowingGoal id p) a) where observer = observer1 ; observers = observers1
