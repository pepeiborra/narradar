{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
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
import Data.Traversable as T (Traversable(..), mapM, fmapDefault, foldMapDefault)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.XHtml (theclass)

import Data.Term
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
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Term
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils (chunks)

import Prelude hiding (pi)

type NarrowingGoal id = MkNarrowingGoal id Rewriting
type CNarrowingGoal id = MkNarrowingGoal id IRewriting

data MkNarrowingGoal id p = forall heu . PolyHeuristic heu id =>
                          NarrowingGoal (Goal id) (AF_ id) (MkHeu heu) p

instance (Ord id, IsProblem p) => IsProblem (MkNarrowingGoal id p)  where
  data Problem (MkNarrowingGoal id p) a = NarrowingGoalProblem {goal::Goal id, pi::AF_ id, baseProblem::Problem p a}
  getProblemType (NarrowingGoalProblem g af p) = narrowingGoal' g af (getProblemType p)
  getR   (NarrowingGoalProblem _ _ p) = getR p

instance (Ord id, IsDPProblem p, MkProblem p trs, HasSignature trs, id ~ SignatureId (Problem p trs)) =>
    MkProblem (MkNarrowingGoal id p) trs where
  mkProblem (NarrowingGoal g af _ base) rr
      = NarrowingGoalProblem g (af `mappend` AF.init p) p where p = mkProblem base rr
  mapR f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (mapR f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (MkNarrowingGoal id p) where
  getP   (NarrowingGoalProblem _ _ p) = getP p

instance (id ~ SignatureId (Problem p trs), HasSignature trs, Ord id, MkDPProblem p trs) =>
    MkDPProblem (MkNarrowingGoal id p) trs where
  mapP f (NarrowingGoalProblem g af p) = NarrowingGoalProblem g af (mapP f p)
  mkDPProblem (NarrowingGoal g af _ base) rr dp = NarrowingGoalProblem g (af `mappend` AF.init p) p
    where p = mkDPProblem base rr dp

narrowingGoal  g = NarrowingGoal g (mkGoalAF g) bestHeu rewriting
cnarrowingGoal g = NarrowingGoal g (mkGoalAF g) bestHeu irewriting
narrowingGoal' g af p = NarrowingGoal g af bestHeu p

mkDerivedNarrowingGoalProblem g mkH p = do
  let heu = mkHeu mkH p
      af  = mkGoalAF g `mappend` AF.init p
  af' <-  Set.toList $ invariantEV heu p af
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
  setBaseProblem p0 p = p{baseProblem = p0}

-- Output

instance Pretty p => Pretty (MkNarrowingGoal id p) where
    pPrint (NarrowingGoal _ _ _ b) = text "NarrowingGoal" <+> pPrint b

instance HTMLClass (MkNarrowingGoal id Rewriting) where htmlClass _ = theclass "NDP"
instance HTMLClass (MkNarrowingGoal id IRewriting) where htmlClass _ = theclass "GNDP"

instance (HasRules t v trs, GetVars v trs, Pretty v, Pretty (t(Term t v))
         ,Pretty id, Pretty (Goal id)
         ,Foldable t, HasId t, id ~ TermId t
         ,PprTPDB (Problem base trs), HasMinimality base
         ) => PprTPDB (Problem (MkNarrowingGoal id base) trs) where
  pprTPDB (NarrowingGoalProblem g pi p) =
      pprTPDB (setMinimality A p) $$
      parens (text "STRATEGY NARROWING") $$
      parens (text "STRATEGY GOAL" <+> g)

-- Icap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (MkNarrowingGoal id p, trs)
  where
    icap (NarrowingGoal _ _ _ p,trs) = icap (p,trs)

-- Usable Rules

instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v), ApplyAF trs
         , id ~ AFId trs, AFId (Term t v) ~ id, Ord id, Ord (t(Term t v))
         ,IUsableRules t v p trs, ICap t v (p,trs)) =>
   IUsableRules t v (MkNarrowingGoal id p) trs
 where
   iUsableRulesM (NarrowingGoal _ pi _ b) trs dps tt = return trs
   iUsableRulesVarM (NarrowingGoal _ _ _ b) = iUsableRulesVarM b

