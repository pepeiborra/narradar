{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
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
data CNarrowing = CNarrowing                          deriving (Eq, Ord, Show)

narrowingProblem         = NarrowingProblem
cnarrowingProblem        = CNarrowingProblem


instance IsProblem Narrowing where
  data Problem Narrowing a = NarrowingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = Narrowing
  getR (NarrowingProblem r _) = r

instance IsDPProblem Narrowing where
  getP   (NarrowingProblem _ p) = p

instance Monoid trs => MkProblem Narrowing trs where
  mkProblem Narrowing rr = narrowingProblem rr mempty
  mapR f (NarrowingProblem r p) = NarrowingProblem (f r) p


instance MkProblem Narrowing trs => MkDPProblem Narrowing trs where
  mkDPProblem Narrowing = narrowingProblem
  mapP f (NarrowingProblem r p) = NarrowingProblem r (f p)

instance (Unify t, HasId t, Enum v, Ord v, Pretty v, Ord (Term t v), Pretty (t(Term t v))) =>
  MkProblem Narrowing (NarradarTRS t v)
 where
  mkProblem Narrowing rr = narrowingProblem rr mempty
  mapR f (NarrowingProblem rr pp) = mkDPProblem' Narrowing (f rr) pp

instance (Unify t, HasId t, Ord (Term t v), Enum v, Ord v, Pretty v, Pretty (t(Term t v))) =>
  MkDPProblem Narrowing (NarradarTRS t v)
 where
  mkDPProblem Narrowing rr dd@DPTRS{} = narrowingProblem rr dd
  mkDPProblem Narrowing rr dd = mkDPProblem' Narrowing rr dd
  mapP f (NarrowingProblem rr pp) = case f pp of
                                    pp'@DPTRS{} -> NarrowingProblem rr pp'
                                    pp' -> mkDPProblem' Narrowing rr pp'

instance IsProblem CNarrowing where
  data Problem CNarrowing a = CNarrowingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = CNarrowing
  getR (CNarrowingProblem r _) = r

instance IsDPProblem CNarrowing where
  getP (CNarrowingProblem _ p) = p

instance Monoid trs => MkProblem CNarrowing trs where
  mkProblem CNarrowing rr = cnarrowingProblem rr mempty
  mapR f (CNarrowingProblem r p) = CNarrowingProblem (f r) p

instance MkProblem CNarrowing trs => MkDPProblem CNarrowing trs where
  mkDPProblem _ = cnarrowingProblem
  mapP f (CNarrowingProblem r p) = CNarrowingProblem r (f p)

instance (Unify t, HasId t, Enum v, Ord v, Pretty v, Ord (Term t v), Pretty (t(Term t v))) =>
  MkProblem CNarrowing (NarradarTRS t v)
 where
  mkProblem CNarrowing rr = cnarrowingProblem rr mempty
  mapR f (CNarrowingProblem rr pp) = mkDPProblem' CNarrowing (f rr) pp

instance (Unify t, HasId t, Ord (Term t v), Enum v, Ord v, Pretty v, Pretty (t(Term t v))) =>
  MkDPProblem CNarrowing (NarradarTRS t v)
 where
  mkDPProblem CNarrowing rr dd@DPTRS{} = cnarrowingProblem rr dd
  mkDPProblem CNarrowing rr dd = mkDPProblem' CNarrowing rr dd
  mapP f (CNarrowingProblem rr pp) = case f pp of
                                    pp'@DPTRS{} -> CNarrowingProblem rr pp'
                                    pp' -> mkDPProblem' CNarrowing rr pp'


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

-- Data.Term instances

-- ICap

instance (Ord v, Unify t) => ICap t v (Narrowing, NarradarTRS t v) where icap (_,trs) = icap (Rewriting,trs)
instance (Ord v, Unify t) => ICap t v (CNarrowing, NarradarTRS t v) where icap (_,trs) = icap (IRewriting,trs)

-- Usable Rules

instance (Enum v, Ord (Term t v), Ord v, HasId t, Unify t) =>
  IUsableRules t v (Narrowing, NarradarTRS t v) where
   iUsableRulesM (typ,trs) tt = do
      (_, trs') <- iUsableRulesM (Rewriting, trs) tt
      return (typ, trs')
   iUsableRulesVarM (_, trs) = iUsableRulesVarM (Rewriting, trs)

instance (Enum v, Ord (Term t v), Ord v, HasId t, Unify t) =>
  IUsableRules t v (CNarrowing, NarradarTRS t v) where
   iUsableRulesM (typ,trs) tt = do
      (_, trs') <- iUsableRulesM (IRewriting, trs) tt
      return (typ, trs')
   iUsableRulesVarM (_, trs) = iUsableRulesVarM (IRewriting, trs)

-- Insert Pairs

instance (Pretty  id, Ord id) =>InsertDPairs Narrowing (NTRS id) where
  insertDPairs = insertDPairsDefault

instance (Pretty id, Ord id) =>InsertDPairs CNarrowing (NTRS id) where
  insertDPairs = insertDPairsDefault
