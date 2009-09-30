{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
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

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr


data Narrowing = Narrowing                          deriving (Eq, Ord, Show)
instance IsProblem Narrowing where
  data Problem Narrowing a = NarrowingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = Narrowing
  getR (NarrowingProblem r _) = r
  mapR f (NarrowingProblem r p) = NarrowingProblem (f r) p

instance IsDPProblem Narrowing where
  getP (NarrowingProblem _ p) = p
  mapP f (NarrowingProblem r p) = NarrowingProblem r (f p)
instance MkDPProblem Narrowing trs where mkDPProblem _ = NarrowingProblem


data CNarrowing = CNarrowing                          deriving (Eq, Ord, Show)
instance IsProblem CNarrowing where
  data Problem CNarrowing a = CNarrowingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = CNarrowing
  getR (CNarrowingProblem r _) = r
  mapR f (CNarrowingProblem r p) = CNarrowingProblem (f r) p

instance IsDPProblem CNarrowing where
  getP (CNarrowingProblem _ p) = p
  mapP f (CNarrowingProblem r p) = CNarrowingProblem r (f p)
instance MkDPProblem CNarrowing trs where mkDPProblem _ = CNarrowingProblem


narrowingProblem         = NarrowingProblem
cNarrowingProblem        = CNarrowingProblem

instance Functor (Problem Narrowing) where fmap f (NarrowingProblem r p) = NarrowingProblem (f r) (f p)
instance Foldable (Problem Narrowing) where foldMap f (NarrowingProblem r p) = f r `mappend` f p
instance Traversable (Problem Narrowing) where traverse f (NarrowingProblem r p) = NarrowingProblem <$> f r <*> f p

instance Functor (Problem CNarrowing) where fmap f (CNarrowingProblem r p) = CNarrowingProblem (f r) (f p)
instance Foldable (Problem CNarrowing) where foldMap f (CNarrowingProblem r p) = f r `mappend` f p
instance Traversable (Problem CNarrowing) where traverse f (CNarrowingProblem r p) = CNarrowingProblem <$> f r <*> f p


instance Pretty Narrowing where pPrint _ = text "Narrowing"
instance Pretty CNarrowing where pPrint _ = text "Constructor Narrowing"

instance HTML Narrowing where toHtml _ = toHtml "Narrowing Problem"
instance HTML CNarrowing where toHtml _ = toHtml "Constructor Narrowing Problem"
instance HTMLClass Narrowing where htmlClass _ = theclass "NDP"
instance HTMLClass CNarrowing where htmlClass _ = theclass "GNDP"

instance GetPairs Narrowing where getPairs _ = getNPairs

getNPairs trs = getPairs Rewriting trs ++ getLPairs trs
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isRootDefined trs lp]

-- ICap

instance (Ord v, Unify t) => ICap t v (Narrowing, NarradarTRS t v) where icap (_,trs) = icap (Rewriting,trs)
instance (Ord v, Unify t) => ICap t v (CNarrowing, NarradarTRS t v) where icap (_,trs) = icap (IRewriting,trs)

-- Usable Rules

instance (Enum v, Ord (Term t v), Ord v, HasId t, Unify t) =>
  IUsableRules t v (Narrowing, NarradarTRS t v) where
   iUsableRulesM (typ,trs) tt = do
      (_, trs') <- iUsableRulesM (Rewriting, trs) tt
      return (typ, trs')
   iUsableRulesVar (_, trs) = iUsableRulesVar (Rewriting, trs)

instance (Enum v, Ord (Term t v), Ord v, HasId t, Unify t) =>
  IUsableRules t v (CNarrowing, NarradarTRS t v) where
   iUsableRulesM (typ,trs) tt = do
      (_, trs') <- iUsableRulesM (IRewriting, trs) tt
      return (typ, trs')
   iUsableRulesVar (_, trs) = iUsableRulesVar (IRewriting, trs)
