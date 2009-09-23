{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
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
instance IsDPProblem Narrowing where
  data DPProblem Narrowing a = NarrowingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = Narrowing
  mkDPProblem    _ = NarrowingProblem
  getR (NarrowingProblem r _) = r
  getP (NarrowingProblem _ p) = p
  mapR f (NarrowingProblem r p) = NarrowingProblem (f r) p
  mapP f (NarrowingProblem r p) = NarrowingProblem r (f p)

data CNarrowing = CNarrowing                          deriving (Eq, Ord, Show)
instance IsDPProblem CNarrowing where
  data DPProblem CNarrowing a = CNarrowingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = CNarrowing
  mkDPProblem    _ = CNarrowingProblem
  getR (CNarrowingProblem r _) = r
  getP (CNarrowingProblem _ p) = p
  mapR f (CNarrowingProblem r p) = CNarrowingProblem (f r) p
  mapP f (CNarrowingProblem r p) = CNarrowingProblem r (f p)

narrowingProblem         = NarrowingProblem
cNarrowingProblem        = CNarrowingProblem

instance Functor (DPProblem Narrowing) where fmap f (NarrowingProblem r p) = NarrowingProblem (f r) (f p)
instance Foldable (DPProblem Narrowing) where foldMap f (NarrowingProblem r p) = f r `mappend` f p
instance Traversable (DPProblem Narrowing) where traverse f (NarrowingProblem r p) = NarrowingProblem <$> f r <*> f p

instance Functor (DPProblem CNarrowing) where fmap f (CNarrowingProblem r p) = CNarrowingProblem (f r) (f p)
instance Foldable (DPProblem CNarrowing) where foldMap f (CNarrowingProblem r p) = f r `mappend` f p
instance Traversable (DPProblem CNarrowing) where traverse f (CNarrowingProblem r p) = CNarrowingProblem <$> f r <*> f p


instance Pretty Narrowing where pPrint _ = text "Narrowing"
instance Pretty CNarrowing where pPrint _ = text "Constructor Narrowing"

instance HTML Narrowing where toHtml _ = toHtml "Narrowing Problem"
instance HTML CNarrowing where toHtml _ = toHtml "Constructor Narrowing Problem"
instance HTMLClass Narrowing where htmlClass _ = theclass "NDP"
instance HTMLClass CNarrowing where htmlClass _ = theclass "GNDP"

instance GetPairs Narrowing where getPairs _ = getNPairs

getNPairs trs = getPairs Rewriting trs ++ getLPairs trs
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isRootDefined trs lp]

instance Ord id => MkNarradarProblem Narrowing (TermF id) where
  type ProblemType Narrowing (TermF id) = Narrowing
  type TermType    Narrowing (TermF id) = TermF (Identifier id)
  mkNarradarProblem = mkNarradarProblemDefault

instance Ord id => MkNarradarProblem CNarrowing (TermF id) where
  type ProblemType CNarrowing (TermF id) = CNarrowing
  type TermType    CNarrowing (TermF id) = TermF(Identifier id)
  mkNarradarProblem = mkNarradarProblemDefault

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v trs) => ICap t v (Narrowing, trs) where icap (_,trs) = icap (Rewriting,trs)
instance (HasRules t v trs, Unify t, GetVars v trs) => ICap t v (CNarrowing, trs) where icap (_,trs) = icap (IRewriting,trs)

instance (Enum v, Ord (Term t v), Unify t, IsTRS t v trs, GetVars v trs, ICap t v trs) =>
  IUsableRules t v (Narrowing, trs) where
   iUsableRulesM (typ,trs) tt = do
      (_, trs') <- iUsableRulesM (Rewriting, trs) tt
      return (typ, trs')
   iUsableRulesVar (_, trs) = iUsableRulesVar (Rewriting, trs)

instance (Enum v, Ord (Term t v), Unify t, IsTRS t v trs, GetVars v trs) =>
  IUsableRules t v (CNarrowing, trs) where
   iUsableRulesM (typ,trs) tt = do
      (_, trs') <- iUsableRulesM (IRewriting, trs) tt
      return (typ, trs')
   iUsableRulesVar (_, trs) = iUsableRulesVar (IRewriting, trs)
