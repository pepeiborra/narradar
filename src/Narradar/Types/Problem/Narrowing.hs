{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Narradar.Types.Problem.Narrowing where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
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


data MkNarrowing base = MkNarrowing base deriving (Eq, Ord, Show)

type Narrowing  = MkNarrowing Rewriting
type CNarrowing = MkNarrowing IRewriting
type INarrowing = MkNarrowing IRewriting

narrowing  = MkNarrowing rewriting
cnarrowing = MkNarrowing irewriting

instance IsProblem b => IsProblem (MkNarrowing b) where
  newtype Problem (MkNarrowing b) a = NarrowingProblem {baseProblem::Problem b a}
  getFramework (NarrowingProblem p) = MkNarrowing (getFramework p)
  getR (NarrowingProblem b) = getR b

instance IsDPProblem b => IsDPProblem (MkNarrowing b) where
  getP (NarrowingProblem b) =  getP b

instance MkProblem b trs => MkProblem (MkNarrowing b) trs where
  mkProblem (MkNarrowing b)   = NarrowingProblem . mkProblem b
  mapR f (NarrowingProblem b) = NarrowingProblem (mapR f b)


instance (MkProblem (MkNarrowing b) trs, MkDPProblem b trs) => MkDPProblem (MkNarrowing b) trs where
  mkDPProblem (MkNarrowing b) r p = NarrowingProblem $ mkDPProblem b r p
  mapP f (NarrowingProblem b) = NarrowingProblem (mapP f b)

deriving instance (Eq (Problem p trs)) => Eq (Problem (MkNarrowing p) trs)
deriving instance (Ord (Problem p trs)) => Ord (Problem (MkNarrowing p) trs)
deriving instance (Show (Problem p trs)) => Show (Problem (MkNarrowing p) trs)


-- Functor

instance Functor (Problem p) => Functor (Problem (MkNarrowing p)) where fmap f (NarrowingProblem p) = NarrowingProblem (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowing p)) where foldMap f (NarrowingProblem p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowing p)) where traverse f (NarrowingProblem p) = NarrowingProblem <$> traverse f p


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
         ,Pretty v, Pretty (t(Term t v)), Pretty (Family.Id t)
         ,Ord v
         ,t ~ Family.TermF trs
         ,v ~ Family.Var trs
         ,Rule t v ~ Family.Rule trs
         ,HasId t, Functor t, Foldable t, MkDPProblem Rewriting trs
         ) => PprTPDB (Problem Narrowing trs) where
  pprTPDB p = pprTPDB (getBaseProblem p) $$ text "(STRATEGY NARROWING)"


instance (Monoid trs, HasRules trs, GetVars trs, Pretty v, Pretty (t(Term t v))
         ,Ord v
         ,t ~ Family.TermF trs
         ,v ~ Family.Var trs
         ,Rule t v ~ Family.Rule trs
         ,HasId t, Pretty (Family.Id t), Functor t, Foldable t, MkDPProblem Rewriting trs
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

instance ICap (st, NarradarTRS t v) => ICap (MkNarrowing st, NarradarTRS t v) where icap = liftIcap

-- Usable Rules

instance (IUsableRules base trs) => IUsableRules (MkNarrowing base) trs where
   iUsableRulesM    = liftUsableRulesM
   iUsableRulesVarM = liftUsableRulesVarM

-- Insert Pairs

instance (Pretty  id, Ord id) =>InsertDPairs Narrowing (NTRS id) where
  insertDPairs = insertDPairsDefault

instance (Pretty id, Ord id) =>InsertDPairs CNarrowing (NTRS id) where
  insertDPairs = insertDPairsDefault

-- Get Pairs

instance GetPairs Narrowing where getPairs _ = getNPairs

getNPairs trs = getPairs rewriting trs ++ getLPairs trs
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isRootDefined trs lp]
