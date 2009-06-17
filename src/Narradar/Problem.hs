{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs, TypeFamilies #-}

module Narradar.Problem where

import Control.Applicative
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), sum, toList)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable as T
import Text.PrettyPrint hiding (char, Mode)
import qualified Text.PrettyPrint as Ppr
import Prelude as P hiding (mapM, pi, sum)

import Control.Monad.Supply
import Narradar.ArgumentFiltering (AF, AF_, ApplyAF(..), init)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPIdentifiers
import Narradar.ProblemType
import Narradar.TRS
import Narradar.Convert
import Narradar.Ppr
import Narradar.Utils
import Narradar.Term
import Narradar.Var

import Data.Term
import Data.Term.Rules

import qualified Language.Prolog.Syntax as Prolog hiding (ident)

---------------------------
-- DP Problems
---------------------------
data ProblemF id (a :: *) = Problem {typ::(ProblemType id), trs::a ,dps :: !a}
     deriving (Eq,Show,Ord)

instance Ord id => HasSignature (Problem id v) id where
  getSignature (Problem _ trs dps) = getSignature trs `mappend` getSignature dps

type Problem  id   v = ProblemG id (TermF id) v
type ProblemG id t v = ProblemF id (NarradarTRSF id t v (Rule t v))

instance (Ord v, Ord id) => Monoid (Problem id v) where
    mempty = Problem Rewriting mempty mempty
    Problem typ1 t1 dp1 `mappend` Problem typ2 t2 dp2 = Problem typ2 (t1 `mappend` t2) (dp1`mappend`dp2)

instance (Ord id, Ord v) => HasRules (TermF id) v (Problem id v) where
    rules (Problem _ dps trs) = rules dps `mappend` rules trs

instance (Ord v, Ord id) => GetFresh (TermF id) v (Problem id v) where getFreshM = getFreshMdefault
instance (Ord v, Ord id) => GetVars v (Problem id v) where getVars = foldMap getVars

mkProblem :: (Ord id) => ProblemType id -> NarradarTRS id v -> NarradarTRS id v -> Problem id v
mkProblem typ@(getAF -> Just pi) trs dps = let p = Problem (typ `withAF` AF.restrictTo (getAllSymbols p) pi) trs dps in p
mkProblem typ trs dps = Problem typ trs dps

mkDPSig (getSignature -> sig@Sig{..}) | dd <- toList definedSymbols =
  sig{definedSymbols = definedSymbols `Set.union` Set.mapMonotonic markDPSymbol definedSymbols
     ,arity          = arity `Map.union` Map.fromList [(markDPSymbol f, getArity sig f) | f <- dd]
     }

instance (Convert (TermN id v) (TermN id' v'), Convert id id', Ord id, Ord id', Ord v') =>
          Convert (Problem id v) (Problem id' v') where
  convert p@Problem{..} = (fmap convert p){typ = fmap convert typ}

instance (Ord id, Ppr id, Ppr v, Ord v) => Ppr (Problem id v) where
    ppr (Problem Prolog{..} _ _) =
            text "Prolog problem." $$
            text "Clauses:" <+> ppr program $$
            text "Goals:" <+> ppr goals

    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps

type PrologProblem v = Problem String v

mkPrologProblem :: Ord v => [AF_ String] -> Prolog.Program String -> PrologProblem v
mkPrologProblem gg pgm = mkProblem (Prolog gg pgm) mempty mempty

isPrologProblem = isProlog . typ

isFullNarrowingProblem = isFullNarrowing . typ
isBNarrowingProblem    = isBNarrowing . typ
isGNarrowingProblem    = isGNarrowing . typ
isAnyNarrowingProblem  = isAnyNarrowing . typ
isRewritingProblem     = isRewriting . typ
getProblemAF           = getAF . typ

-- -------------
-- AF Problems
-- -------------

class WithAF t id | t -> id where
  withAF :: t -> AF_ id -> t
  stripGoal    :: t -> t

instance (WithAF (ProblemType id) id) => WithAF (Problem id v) id where
  withAF(Problem typ trs dps) goal = Problem (withAF typ goal) trs dps
  stripGoal (Problem typ trs dps)      = Problem (stripGoal  typ)      trs dps

instance WithAF (ProblemType id) id where
  withAF pt@NarrowingModes{..}   pi' = pt{pi=pi'}
  withAF pt@BNarrowingModes{..}  pi' = pt{pi=pi'}
  withAF pt@GNarrowingModes{..}  pi' = pt{pi=pi'}
  withAF pt@LBNarrowingModes{..} pi' = pt{pi=pi'}
  withAF Narrowing   pi = narrowingModes0{pi}
  withAF BNarrowing  pi = bnarrowingModes0{pi}
  withAF GNarrowing  pi = gnarrowingModes0{pi}
  withAF LBNarrowing pi = lbnarrowingModes0{pi}
  withAF Rewriting   _  = Rewriting
--  withAF typ _ = error ("withAF - error: " ++ show(ppr typ))
  stripGoal NarrowingModes{}  = Narrowing
  stripGoal BNarrowingModes{} = BNarrowing
  stripGoal GNarrowingModes{} = GNarrowing
  stripGoal LBNarrowingModes{}= LBNarrowing
  stripGoal m = m
--  withAF typ@Prolog{} _ =

instance (Ord id, Ord v) => ApplyAF (Problem id v) id where
    apply pi p@(Problem typ trs dps) = Problem typ (apply pi trs) (apply pi dps)

-- ------------------
-- Functor Instances
-- ------------------

$(derive makeFunctor     ''ProblemF)
$(derive makeFoldable    ''ProblemF)
$(derive makeTraversable ''ProblemF)
