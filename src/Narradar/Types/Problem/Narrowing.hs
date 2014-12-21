{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ConstraintKinds #-}

module Narradar.Types.Problem.Narrowing where

import Control.Applicative
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad.Free
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import Text.XHtml (HTML(..), theclass)

import Data.Term
import qualified Data.Term.Family as Family
import Data.Term.Rules

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework
import Narradar.Framework.Ppr

import Debug.Hoed.Observe

newtype MkNarrowing base = MkNarrowing base
                         deriving (Eq, Ord, Show, Typeable, Generic, Generic1, NFData)

type Narrowing  = MkNarrowing Rewriting
type CNarrowing = MkNarrowing IRewriting
type INarrowing = MkNarrowing IRewriting

narrowing  = MkNarrowing rewriting
cnarrowing = MkNarrowing irewriting

instance IsProblem b => IsProblem (MkNarrowing b) where
  newtype Problem (MkNarrowing b) a = NarrowingProblem {baseProblem::Problem b a} deriving (Generic)
  getFramework (NarrowingProblem p) = MkNarrowing (getFramework p)
  getR (NarrowingProblem b) = getR b

instance IsDPProblem b => IsDPProblem (MkNarrowing b) where
  getP (NarrowingProblem b) =  getP b

instance MkProblem b trs => MkProblem (MkNarrowing b) trs where
  mkProblem (MkNarrowing b)   = NarrowingProblem . mkProblem b
  mapRO o f (NarrowingProblem b) = NarrowingProblem (mapRO o f b)
  setR_uncheckedO o rr p = p{baseProblem = setR_uncheckedO o rr (baseProblem p)}

instance (MkProblem (MkNarrowing b) trs, MkDPProblem b trs) => MkDPProblem (MkNarrowing b) trs where
  mkDPProblemO o (MkNarrowing b) r p = NarrowingProblem $ mkDPProblemO o b r p
  mapPO o f (NarrowingProblem b) = NarrowingProblem (mapPO o f b)
  setP_uncheckedO obs pp p = p{ baseProblem = setP_uncheckedO obs pp (baseProblem p)}

deriving instance (Eq (Problem p trs)) => Eq (Problem (MkNarrowing p) trs)
deriving instance (Ord (Problem p trs)) => Ord (Problem (MkNarrowing p) trs)
deriving instance (Show (Problem p trs)) => Show (Problem (MkNarrowing p) trs)

instance HasSignature (Problem b a) => HasSignature (Problem (MkNarrowing b) a) where
  getSignature = getSignature . baseProblem


-- Functor

deriving instance Functor (Problem p) => Functor (Problem (MkNarrowing p))
deriving instance Foldable (Problem p) => Foldable (Problem (MkNarrowing p))
deriving instance Traversable (Problem p) => Traversable (Problem (MkNarrowing p))


-- Data.Term instances

-- Output

instance HTML Narrowing where toHtml _ = toHtml "Narrowing Problem"
instance HTML CNarrowing where toHtml _ = toHtml "Constructor Narrowing Problem"
instance HTMLClass Narrowing where htmlClass _ = theclass "NDP"
instance HTMLClass CNarrowing where htmlClass _ = theclass "GNDP"

instance Pretty base => Pretty (MkNarrowing base) where
  pPrint (MkNarrowing base) = text "Narrowing" <+> parens base

instance Pretty Narrowing where
  pPrint (MkNarrowing (MkRewriting Standard M)) = text "Narrowing"
  pPrint (MkNarrowing (MkRewriting Standard A)) = text "Narrowing (no minimality)"

instance Pretty INarrowing where
  pPrint (MkNarrowing (MkRewriting Innermost M)) = text "Narrowing (innermost strategy)"
  pPrint (MkNarrowing (MkRewriting Innermost A)) = text "Narrowing (innermost strategy, no minimality)"

instance (Monoid trs, HasRules trs, GetVars trs
         ,Pretty v, PprTPDB v, Pretty (t(Term t v)), Pretty (Family.Id t)
         ,Ord v
         ,t ~ Family.TermF trs
         ,v ~ Family.Var trs
         ,Rule t v ~ Family.Rule trs
         ,HasId1 t, Functor t, Foldable t, MkDPProblem Rewriting trs
         ) => PprTPDB (Problem Narrowing trs) where
  pprTPDB p = pprTPDB (getBaseProblem p) $$ text "(STRATEGY NARROWING)"


instance (Monoid trs, HasRules trs, GetVars trs, Pretty v, Pretty (t(Term t v))
         ,PprTPDB v, Ord v
         ,t ~ Family.TermF trs
         ,v ~ Family.Var trs
         ,Rule t v ~ Family.Rule trs
         ,HasId1 t, Pretty (Family.Id t), Functor t, Foldable t, MkDPProblem Rewriting trs
         ) => PprTPDB (Problem CNarrowing trs) where
  pprTPDB p = pprTPDB (getBaseProblem p) $$ text "(STRATEGY CNARROWING)"


-- Framework Extension

instance FrameworkExtension MkNarrowing where
  getBaseFramework (MkNarrowing b) = b
  getBaseProblem   (NarrowingProblem p) = p
  liftProblem   f p = f (baseProblem p) >>= \p0' -> return p{baseProblem = p0'}
  liftFramework f (MkNarrowing b) = MkNarrowing (f b)
  liftProcessorS = liftProcessorSdefault

-- ICap

instance ICap (Problem p (NarradarTRS t v))
              => ICap (Problem (MkNarrowing p) (NarradarTRS t v)) where
  icapO = liftIcapO

-- Usable Rules

instance ( IUsableRules (Problem base trs)
         , FrameworkProblem (MkNarrowing base) trs
         , IsProblem base
         ) => IUsableRules (Problem (MkNarrowing base) trs) where
   iUsableRulesM    = liftUsableRulesM
   iUsableRulesVarM = liftUsableRulesVarM

-- Insert Pairs

instance (FrameworkProblemN (MkNarrowing base) id
         ) =>InsertDPairs (MkNarrowing base) (NTRS id) where
  insertDPairsO = insertDPairsDefault

instance (FrameworkProblemN (MkNarrowing base) id
         ) => ExpandDPair (MkNarrowing base) (NTRS id) where
  expandDPairO = expandDPairOdefault

-- Get Pairs

instance GetPairs Narrowing where getPairs _ = getNPairs

getNPairs trs = getPairs rewriting trs ++ getLPairs trs
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isRootDefined trs lp]

-- Observe
instance Observable1 MkNarrowing
instance Observable st => Observable (MkNarrowing st) where
  observer = observer1 ; observers = observers1

instance (Observable1 (Problem p)) => Observable1 (Problem (MkNarrowing p)) where
  observer1 (NarrowingProblem p) = send "NarrowingProblem" (return NarrowingProblem << p)

instance (Observable a, Observable1(Problem p)) => Observable (Problem (MkNarrowing p) a) where
  observer = observer1
  observers = observers1
