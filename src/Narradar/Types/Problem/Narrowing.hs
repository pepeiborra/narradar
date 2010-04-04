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

narrowing  = MkNarrowing rewriting
cnarrowing = MkNarrowing irewriting

instance IsProblem b => IsProblem (MkNarrowing b) where
  newtype Problem (MkNarrowing b) a = NarrowingProblem (Problem b a)
  getProblemType (NarrowingProblem p) = MkNarrowing (getProblemType p)
  getR (NarrowingProblem b) = getR b

instance IsDPProblem b => IsDPProblem (MkNarrowing b) where
  getP (NarrowingProblem b) =  getP b

instance MkProblem b trs => MkProblem (MkNarrowing b) trs where
  mkProblem (MkNarrowing b)   = NarrowingProblem . mkProblem b
  mapR f (NarrowingProblem b) = NarrowingProblem (mapR f b)


instance (MkProblem (MkNarrowing b) trs, MkDPProblem b trs) => MkDPProblem (MkNarrowing b) trs where
  mkDPProblem (MkNarrowing b) r p = NarrowingProblem $ mkDPProblem b r p
  mapP f (NarrowingProblem b) = NarrowingProblem (mapP f b)


instance FrameworkExtension MkNarrowing where
    getBaseFramework (MkNarrowing b) = b
    getBaseProblem   (NarrowingProblem p) = p
    setBaseProblem p (NarrowingProblem _) = NarrowingProblem p

deriving instance (Eq (Problem p trs)) => Eq (Problem (MkNarrowing p) trs)
deriving instance (Ord (Problem p trs)) => Ord (Problem (MkNarrowing p) trs)
deriving instance (Show (Problem p trs)) => Show (Problem (MkNarrowing p) trs)

instance Functor (Problem p) => Functor (Problem (MkNarrowing p)) where fmap f (NarrowingProblem p) = NarrowingProblem (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowing p)) where foldMap f (NarrowingProblem p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowing p)) where traverse f (NarrowingProblem p) = NarrowingProblem <$> traverse f p

instance Pretty Narrowing where pPrint _ = text "Narrowing"
instance Pretty CNarrowing where pPrint _ = text "Constructor Narrowing"

instance HTML Narrowing where toHtml _ = toHtml "Narrowing Problem"
instance HTML CNarrowing where toHtml _ = toHtml "Constructor Narrowing Problem"
instance HTMLClass Narrowing where htmlClass _ = theclass "NDP"
instance HTMLClass CNarrowing where htmlClass _ = theclass "GNDP"

instance GetPairs Narrowing where getPairs _ = getNPairs

getNPairs trs = getPairs rewriting trs ++ getLPairs trs
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isRootDefined trs lp]


-- Data.Term instances

-- Output

instance (Monoid trs, HasRules t v trs, GetVars v trs, Pretty v, Pretty (t(Term t v))
         ,HasId t, Pretty (TermId t), Foldable t, MkDPProblem Rewriting trs
         ) => PprTPDB (Problem Narrowing trs) where
  pprTPDB p = pprTPDB (getBaseProblem p) $$ text "(STRATEGY NARROWING)"


instance (Monoid trs, HasRules t v trs, GetVars v trs, Pretty v, Pretty (t(Term t v))
         ,HasId t, Pretty (TermId t), Foldable t, MkDPProblem Rewriting trs
         ) => PprTPDB (Problem CNarrowing trs) where
  pprTPDB p = pprTPDB (getBaseProblem p) $$ text "(STRATEGY CNARROWING)"


-- ICap

instance ICap t v (st, NarradarTRS t v) => ICap t v (MkNarrowing st, NarradarTRS t v) where icap = liftIcap

-- Usable Rules

instance (IUsableRules t v base trs) => IUsableRules t v (MkNarrowing base) trs where
   iUsableRulesM    = liftUsableRulesM
   iUsableRulesVarM = liftUsableRulesVarM

-- Insert Pairs

instance (Pretty  id, Ord id) =>InsertDPairs Narrowing (NTRS id) where
  insertDPairs = insertDPairsDefault

instance (Pretty id, Ord id) =>InsertDPairs CNarrowing (NTRS id) where
  insertDPairs = insertDPairsDefault
