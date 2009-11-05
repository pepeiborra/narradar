{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Narradar.Types.Problem.NarrowingGen where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Char
import Data.Foldable (Foldable(..), toList)
import Data.List (nub)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Maybe
import Data.Monoid
import Data.Typeable
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
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Framework.Ppr
import Narradar.Utils

import Prelude hiding (pi)

-- -----------------------
-- Terms with Gen and Goal
-- -----------------------

data GenId id = AnId id | GenId | GoalId deriving (Eq, Ord, Show, Typeable)

instance Pretty id => Pretty (GenId id) where
  pPrint GenId  = text "GEN"
  pPrint GoalId = text "GOAL"
  pPrint (AnId id) = pPrint id

instance Pretty (GenId String) where
  pPrint GenId  = text "GEN"
  pPrint GoalId = text "GOAL"
  pPrint (AnId id) = text id

class GenSymbol id where
  goalSymbol :: id
  genSymbol  :: id

instance GenSymbol (GenId id) where genSymbol = GenId; goalSymbol = GoalId
instance GenSymbol a => GenSymbol (Identifier a) where genSymbol = IdFunction genSymbol; goalSymbol = IdFunction goalSymbol

-- --------------------------------------------------------------
-- The class of Narrowing-as-Rewriting-with-Generators problems
-- --------------------------------------------------------------
type NarrowingGen  = MkNarrowingGen Rewriting
type CNarrowingGen = MkNarrowingGen IRewriting
instance GetPairs NarrowingGen where getPairs _ = getNPairs

data MkNarrowingGen p = NarrowingGen {baseProblemType :: p} deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance IsProblem p => IsProblem (MkNarrowingGen p) where
  data Problem (MkNarrowingGen p) a    = NarrowingGenProblem {baseProblem::Problem p a}
  getProblemType (NarrowingGenProblem p) = NarrowingGen (getProblemType p)
  getR   (NarrowingGenProblem p) = getR p

instance MkProblem p trs => MkProblem (MkNarrowingGen p) trs where
  mkProblem (NarrowingGen p) rr = NarrowingGenProblem (mkProblem p rr)
  mapR f (NarrowingGenProblem p) = NarrowingGenProblem (mapR f p)

instance IsDPProblem p => IsDPProblem (MkNarrowingGen p) where
  getP   (NarrowingGenProblem p) = getP p


instance (Ord id, GenSymbol id, MkDPProblem p (NTRS id)) =>
  MkDPProblem (MkNarrowingGen p) (NTRS id)
 where
  mapP f (NarrowingGenProblem p) = NarrowingGenProblem (mapP f p)
  mkDPProblem (NarrowingGen typ) trs dps = narrowingGenProblem $ mkDPProblem typ trs' dps'
   where
    trs' = mapNarradarTRS' id extraVarsToGen trs
    dps' = mapNarradarTRS' id extraVarsToGen dps

narrowingGen        = NarrowingGen  Rewriting
cnarrowingGen       = NarrowingGen  IRewriting
narrowingGenProblem = NarrowingGenProblem

-- ----------
-- Instances
-- ----------

deriving instance (Eq (Problem p trs)) => Eq (Problem (MkNarrowingGen p) trs)
deriving instance (Ord (Problem p trs)) => Ord (Problem (MkNarrowingGen p) trs)
deriving instance (Show (Problem p trs)) => Show (Problem (MkNarrowingGen p) trs)

-- Functor

instance Functor (Problem p) => Functor (Problem (MkNarrowingGen p)) where fmap f (NarrowingGenProblem p) = NarrowingGenProblem (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowingGen p)) where foldMap f (NarrowingGenProblem p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowingGen p)) where traverse f (NarrowingGenProblem p) = NarrowingGenProblem <$> traverse f p

-- Data.Term instances

-- Output

instance Pretty p => Pretty (MkNarrowingGen p) where
    pPrint NarrowingGen{..} = text "NarrowingGen" <+> pPrint baseProblemType

instance HTMLClass (MkNarrowingGen Rewriting) where htmlClass _ = theclass "GenNarr"
instance HTMLClass (MkNarrowingGen IRewriting) where htmlClass _ = theclass "GenCNarr"

-- Custom Argument Filtering notion

instance ( GenSymbol id, Ord id, Functor (Problem base)
         , id ~ AFId (Problem (MkNarrowingGen base) (NTRS id))
         ) => ApplyAF (Problem (MkNarrowingGen base) (NTRS id)) where
  type AFId (Problem (MkNarrowingGen base) (NTRS id)) = AFId (NTRS id)
  apply af = fmap (mapNarradarTRS' id extraVarsToGen . apply af)

-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (MkNarrowingGen p, trs)
  where
    icap (NarrowingGen{..},trs) = icap (baseProblemType,trs)

-- Usable Rules

instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,IUsableRules t v (p,trs, trs), ICap t v (p,trs)) =>
   IUsableRules t v (MkNarrowingGen p, trs, trs)
 where
   iUsableRulesM (typ@NarrowingGen{..}, trs, dps) tt = do
      (_,trs',dps') <- iUsableRulesM (baseProblemType,trs,dps) tt
      return (typ, trs',dps')

   iUsableRulesVarM (NarrowingGen{..},trs, dps) = iUsableRulesVarM (baseProblemType, trs, dps)

-- Insert Pairs

instance (MkDPProblem (MkNarrowingGen base) trs, InsertDPairs base trs) => InsertDPairs (MkNarrowingGen base) trs where
  insertDPairs NarrowingGenProblem{..} = narrowingGenProblem . insertDPairs baseProblem


-- -------------------
-- Support functions
-- -------------------

extraVarsToGen (l :-> r) = l :-> applySubst sigma r
     where
      sigma = fromListSubst (evars `zip` repeat genTerm)
      genTerm = term genSymbol []
      evars = Set.toList(getVars r `Set.difference` getVars l)
