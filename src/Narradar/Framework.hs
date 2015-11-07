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
        module Narradar.Framework.Observe,
        module MuTerm.Framework.Problem,
        module MuTerm.Framework.Processor,
        module MuTerm.Framework.Proof,
        module MuTerm.Framework.Strategy)
  where

import Control.Exception (Exception)
import Control.Monad.Free
import Control.Monad.Identity
import Control.DeepSeq (NFData(..))
import Control.DeepSeq.Extras (NFData1)
import Data.Foldable (toList, Foldable, foldMap)
import Data.Functor.Constant
import Data.Hashable (Hashable)
import Data.Traversable (Traversable)
import Data.Typeable
import Prelude.Extras

import Data.Term (foldTerm, getId, Rename, Term, Unify, HasId1)
import qualified Data.Term as Family
import Data.Rule.Family as Family
import Data.Term.Substitutions

import MuTerm.Framework.DotRep
import MuTerm.Framework.Problem
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy

import Narradar.Framework.Constraints
import Narradar.Framework.Observe
import Narradar.Framework.Ppr
import Narradar.Types.ArgumentFiltering (ApplyAF)
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term (HasArity)
import Narradar.Utils ((<$$>))

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

type FrameworkTyp a  = (Eq a, Typeable a, Pretty a, IsDPProblem a, Observable a, Observable1(Problem a), NFData a, Traversable (Problem a), HasMinimality a)
type FrameworkVar v  = (Enum v, Ord v, NFData v, Pretty v, Rename v, Typeable v, PprTPDB v, Observable v)
type FrameworkT   t  = (Unify t, HasId1 t, Traversable t, Typeable t, Observable1 t, FrameworkId (Family.Id t), Ord1 t, NFData1 t)
type FrameworkId id  = (NFData id, Pretty id, Ord id, Observable id, Typeable id, Show id, Hashable id, NFData id, RemovePrologId id, HasArity id)
type FrameworkTerm t v = (FrameworkVar v, FrameworkT t, FrameworkId (Family.Id t)
                         ,Ord(Term t v), Pretty(Term t v), NFData(Term t v)
                         ,Observable (Term t v), ApplyAF (Term t v))

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
                        , trs ~ Trs tag (Problem base trs)
                        , base' ~ Typ tag (Problem base trs)
                        , Info (InfoConstraint tag) (Problem base trs)
                        , Info (InfoConstraint tag) (Problem base' trs)
                        ) =>
                        Observer -> tag -> Problem (ext base) trs -> Proof (InfoConstraint tag) (Problem (ext base') trs)
    liftProcessorS :: ( Typeable base, Typeable base', Typeable trs
                      , Processor tag (Problem base trs)
                      , trs ~ Trs tag (Problem base trs)
                      , base' ~ Typ tag (Problem base trs)
                      , Info (InfoConstraint tag) (Problem base trs)
                      , Info (InfoConstraint tag) (Problem base' trs)
                     ) => Observer -> tag -> Problem (ext base) trs -> [Proof (InfoConstraint tag) (Problem (ext base') trs)]

    liftProcessor o = liftProblem . applyO o
    liftProcessorS  = liftProcessorSdefault

liftProcessorSdefault o tag = untrans . liftProblem (trans' . applySearchO o tag)

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

instance NFData (Strategy st) where rnf _ = ()

class IsDPProblem typ => HasStrategy typ st | typ -> st where
  getStrategy :: typ -> Strategy st

instance (FrameworkExtension ext, IsDPProblem (ext b), HasStrategy b st) => HasStrategy (ext b) st where
  getStrategy = getStrategy . getBaseFramework

instance Observable1 (Strategy) where
  observer1 Standard  = send "Standard"  (return Standard)
  observer1 Innermost = send "Innermost" (return Innermost)
instance Observable a => Observable(Strategy a) where
  observer = observer1
  observers = observers1
instance Observable Standard where observer _ = undefined
instance Observable Innermost where observer _ = undefined
instance NFData Standard
instance NFData Innermost

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

-- ----------------
-- Other instances
-- ----------------
instance (Observable1 (Problem typ), Observable trs) => Observable (Problem typ trs) where
  observer = observer1
  observers = observers1
