{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Narradar.Framework (
        module Narradar.Framework,
        module MuTerm.Framework.Problem,
        module MuTerm.Framework.Processor,
        module MuTerm.Framework.Proof,
        module MuTerm.Framework.Strategy)
  where

import Control.Exception (Exception)
import Control.Monad.Free
import Control.Monad.Identity
import Data.Foldable (toList, Foldable, foldMap)
import Data.Functor.Constant
import Data.Hashable (Hashable)
import Data.Traversable (Traversable)
import Data.Typeable

import Data.Term (foldTerm, getId, Rename, Term, Match, Unify, HasId)
import qualified Data.Term as Family
import Data.Rule.Family as Family
import Data.Term.Variables

import MuTerm.Framework.DotRep
import MuTerm.Framework.Problem
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy

import Narradar.Framework.Ppr
import Narradar.Types.ArgumentFiltering (ApplyAF)
import Narradar.Types.DPIdentifiers
import Narradar.Utils ((<$$>))
import Control.DeepSeq (NFData)

import GHC.Generics (Generic)
import Debug.Hoed.Observe

type instance Family.Id    (Problem typ trs) = Family.Id trs
type instance Family.TermF (Problem typ trs) = Family.TermF trs
type instance Family.Var   (Problem typ trs) = Family.Var trs
type instance Family.Rule  (Problem typ trs) = Family.Rule trs

instance (GetVars trs, Foldable (Problem typ)) => GetVars (Problem typ trs) where getVars = foldMap getVars

-- ---------------------
-- Framework constraints
-- ---------------------

type FrameworkTyp a  = (Eq a, Typeable a, Pretty a, IsDPProblem a, Observable a, {- NFData a,-} Traversable (Problem a), HasMinimality a)
type FrameworkVar v  = (Enum v, Ord v, Pretty v, Rename v, Typeable v, PprTPDB v, Observable v)
type FrameworkT   t  = (Match t, Unify t, HasId t, Foldable t, Typeable t, Observable1 t)
type FrameworkId id  = (Pretty id, Ord id, Observable id, Typeable id, Show id, Hashable id)
type FrameworkTerm t v = (FrameworkVar v, FrameworkT t, Ord(Term t v), Pretty(Term t v), Observable (Term t v), ApplyAF (Term t v))

-- ----------------------
-- Framework extensions
-- ----------------------

class FrameworkExtension ext where
    getBaseFramework :: ext base -> base
    getBaseProblem   :: Problem (ext base) trs -> Problem base trs
    liftProblem   :: (Monad m) => (Problem base trs -> m(Problem base' trs)) ->
                                 Problem (ext base) trs -> m(Problem (ext base') trs)
    liftFramework :: (base -> base') -> ext base -> ext base'
    liftProcessor    :: ( Processor tag (Problem base trs)
                        , Trs tag (Problem base trs) ~ trs
                        , base' ~ Typ tag (Problem base trs)
                        , Info (InfoConstraint tag) (Problem base trs)
                        , Info (InfoConstraint tag) (Problem base' trs)
                        , MonadPlus m, Traversable m, Observable1 m
                        ) =>
                        tag -> Problem (ext base) trs -> Proof (InfoConstraint tag) m (Problem (ext base') trs)
    liftProcessorS :: ( Processor tag (Problem base trs)
                      , Trs tag (Problem base trs) ~ trs
                      , base' ~ Typ tag (Problem base trs)
                      , Info (InfoConstraint tag) (Problem base trs)
                      , Info (InfoConstraint tag) (Problem base' trs)
                      , MonadPlus m, Traversable m, Observable1 m
                     ) => tag -> Problem (ext base) trs -> [Proof (InfoConstraint tag) m (Problem (ext base') trs)]

    liftProcessor  = liftProblem . apply
    liftProcessorS = liftProcessorSdefault

liftProcessorSdefault tag = untrans . liftProblem (trans' . applySearch tag)

setBaseProblem :: FrameworkExtension ext => Problem base' trs -> Problem (ext base) trs -> Problem (ext base') trs
setBaseProblem p = runIdentity . liftProblem (const $ return p)

getBaseProblemFramework :: (FrameworkExtension ext, IsProblem (ext base)) => Problem (ext base) trs -> base
getBaseProblemFramework = getBaseFramework . getFramework

-- ---------- --
-- Strategies --
-- ---------- --

data Standard  deriving (Generic, Typeable)
data Innermost deriving (Generic, Typeable)
data Strategy st where
    Standard  :: Strategy Standard
    Innermost :: Strategy Innermost
  deriving Typeable

class IsDPProblem typ => HasStrategy typ st | typ -> st where
  getStrategy :: typ -> Strategy st

instance (FrameworkExtension ext, IsDPProblem (ext b), HasStrategy b st) => HasStrategy (ext b) st where
  getStrategy = getStrategy . getBaseFramework

instance Observable1 (Strategy) where
  observer1 Standard  = send "Standard"  (return Standard)
  observer1 Innermost = send "Innermost" (return Innermost)
instance Observable Standard where observer _ = undefined
instance Observable Innermost where observer _ = undefined

-- ---------- --
-- Minimality --
-- ---------- --

data Minimality  = M | A   deriving (Eq, Ord, Show, Generic)

instance NFData Minimality

class IsDPProblem typ => HasMinimality typ where
  getMinimality :: typ -> Minimality
  setMinimality :: Minimality -> Problem typ trs -> Problem typ trs

getMinimalityFromProblem :: HasMinimality typ => Problem typ trs -> Minimality
getMinimalityFromProblem = getMinimality . getFramework

instance (IsDPProblem (p b), HasMinimality b, FrameworkExtension p) => HasMinimality (p b)
   where getMinimality = getMinimality . getBaseFramework
         setMinimality m = runIdentity . liftProblem (return . setMinimality m)

instance Observable Minimality

-- -------------
-- forDPProblem
-- -------------

forDPProblem f p = f (getFramework p) (getR p) (getP p)

-- ---------------------
-- Framework Exceptions
-- ---------------------

data TimeoutException = TimeoutException deriving (Show, Typeable)
instance Exception TimeoutException
