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
import Narradar.Utils

import TRS hiding (ppr, Ppr, unify, unifies)
import qualified TRS
import qualified Language.Prolog.Syntax as Prolog hiding (ident)

---------------------------
-- DP Problems
---------------------------
data ProblemF id a = Problem {typ::(ProblemType id), trs::a ,dps :: !a}
     deriving (Eq,Show)

instance Size a => Size (ProblemF id a) where size = sum . fmap size
instance Ord id => HasSignature (ProblemG id f) id where
  {-# SPECIALIZE instance HasSignature (Problem BBasicId) Id #-}
  getSignature (Problem _ trs dps) = getSignature trs `mappend` getSignature dps
--  getSignature PrologProblem{} = error "getSignature: tried to get the signature of a PrologProblem"

type Problem     f = ProblemG Id f
type ProblemG id f = ProblemF id (NarradarTRS id f)

instance (Ord (Term f), TRSC f, Ord id, T id :<: f) => Monoid (ProblemG id f) where
    mempty = Problem Rewriting mempty mempty
    Problem typ1 t1 dp1 `mappend` Problem typ2 t2 dp2 = Problem typ2 (t1 `mappend` t2) (dp1`mappend`dp2)

instance (Ord id, TRSC f, T id :<: f) => TRS (ProblemG id f) id f where
    rules (Problem _ trs dps) = rules trs `mappend` rules dps

mkProblem :: (Show id, Ord id) => ProblemType id -> NarradarTRS id f -> NarradarTRS id f -> ProblemG id f
mkProblem typ@(getAF -> Just pi) trs dps = let p = Problem (typ `withGoalAF` AF.restrictTo (getAllSymbols p) pi) trs dps in p
mkProblem typ trs dps = Problem typ trs dps

mkDPSig (getSignature -> sig@Sig{..}) | dd <- toList definedSymbols =
  sig{definedSymbols = definedSymbols `Set.union` Set.mapMonotonic markDPSymbol definedSymbols
     ,arity          = arity `Map.union` Map.fromList [(markDPSymbol f, getArity sig f) | f <- dd]
     }

instance (ConvertT f f', Convert id id', Ord id, Ord id', T id :<: f, T id' :<: f', TRSC f, TRSC f' ) => Convert (ProblemG id f) (ProblemG id' f') where
  convert p@Problem{..} = (fmap convert p){typ = fmap convert typ}

instance TRS.Ppr f => Ppr (ProblemG id f) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps

type PrologProblem = ProblemG String Basic'
mkPrologProblem :: [AF_ String] -> Prolog.Program String -> PrologProblem
mkPrologProblem gg pgm = mkProblem (Prolog gg pgm) mempty mempty

isPrologProblem = isProlog . typ

isFullNarrowingProblem = isFullNarrowing . typ
isBNarrowingProblem    = isBNarrowing . typ
isGNarrowingProblem    = isGNarrowing . typ
isAnyNarrowingProblem  = isAnyNarrowing . typ
isRewritingProblem     = isRewriting . typ

-- -------------
-- AF Problems
-- -------------

class WithGoalAF t id where
  type T' t id :: *
  withGoalAF :: t -> AF_ id -> T' t id

instance (WithGoalAF (ProblemType id) id) => WithGoalAF (ProblemG id f) id where
  type T' (ProblemG id f) id = ProblemG id f
  withGoalAF(Problem typ trs dps) goal = Problem (withGoalAF typ goal) trs dps

instance (Show id) =>  WithGoalAF (ProblemType id) id where
  type T' (ProblemType id) id = ProblemType id
  withGoalAF pt@NarrowingModes{..}   pi' = pt{pi=pi'}
  withGoalAF pt@BNarrowingModes{..}  pi' = pt{pi=pi'}
  withGoalAF pt@GNarrowingModes{..}  pi' = pt{pi=pi'}
  withGoalAF pt@LBNarrowingModes{..} pi' = pt{pi=pi'}
  withGoalAF Narrowing   pi = narrowingModes0{pi}
  withGoalAF BNarrowing  pi = bnarrowingModes0{pi}
  withGoalAF GNarrowing  pi = gnarrowingModes0{pi}
  withGoalAF LBNarrowing pi = lbnarrowingModes0{pi}
  withGoalAF Rewriting   _  = Rewriting
--  withGoalAF typ@Prolog{} _ =
  withGoalAF typ _ = error ("withGoalAF - error: " ++ show typ)

instance (Ord id) => ApplyAF (ProblemG id f) id where
    {-# SPECIALIZE instance ApplyAF (Problem BBasicId) Id #-}
    apply pi p@(Problem typ trs dps) = Problem typ (apply pi trs) (apply pi dps)

-- ------------------
-- Functor Instances
-- ------------------

$(derive makeFunctor     ''ProblemF)
$(derive makeFoldable    ''ProblemF)
$(derive makeTraversable ''ProblemF)
