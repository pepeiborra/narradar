{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Narradar.Types.Problem.NonDP where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Exception (assert)
import Data.Foldable as F (Foldable(..), toList)
import Data.Monoid
import Data.Traversable as T (Traversable(..), mapM)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import Text.XHtml (HTML(..), theclass)

import Data.Term
import qualified Data.Term.Family as Family
import Data.Term.Rules

import Narradar.Constraints.UsableRules
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr

import GHC.Generics (Generic)
import Debug.Hoed.Observe

{-
   Problem type for modelling a TRS termination problem, out of the dependency pair framework.

   The instance for the GetPairs  type class has a bogus implementations that returns the empty set.
   In addition, instances for the IsDPProblem and MkDPProblem type classes are provided.
   This is on purpose, to avoid changes in the Narradar framework code that constructs termination problems,
   as said code is built on the assumption that all the termination problems are DP problems.

   There is an associated ToDP processor that allows to convert a (NonDP Foo) problem to a Foo problem.
 -}

newtype NonDP a = NonDP { nonDP :: a }
                  deriving (Eq,Ord,Show,Generic,Generic1,Typeable,NFData,
                            Functor,Foldable,Traversable
                           )

instance Pretty a => Pretty (NonDP a)
    where
         pPrint (NonDP p) = pPrint p <+> text "(non DP)"

--instance HasSignature a => HasSignature (NonDP a) where  getSignature = getSignature . nonDP

instance IsProblem a => IsProblem (NonDP a) where
  newtype Problem (NonDP a) trs = NonDPProblem { nonDPProblem :: Problem a trs}  deriving (Generic1)
  getFramework = NonDP . getFramework . nonDPProblem
  getR = getR . nonDPProblem

instance MkProblem a trs => MkProblem (NonDP a) trs where
  mkProblem (NonDP a) = NonDPProblem . mkProblem a
  mapRO o f = NonDPProblem . mapRO o f . nonDPProblem
  setR_uncheckedO o rr = NonDPProblem . setR_uncheckedO o rr . nonDPProblem

instance HasSignature (Problem a trs) => HasSignature (Problem (NonDP a) trs) where getSignature = getSignature . nonDPProblem

instance FrameworkExtension NonDP where
  getBaseFramework  = nonDP
  getBaseProblem    = nonDPProblem
  liftFramework f (NonDP p) = NonDP (f p)
  liftProblem   f p = f (getBaseProblem p) >>= \p0' -> return p{nonDPProblem = p0'}
  liftProcessorS = liftProcessorSdefault

deriving instance Eq      (Problem a trs) => Eq      (Problem (NonDP a) trs)
deriving instance Ord     (Problem a trs) => Ord     (Problem (NonDP a) trs)
deriving instance Show    (Problem a trs) => Show    (Problem (NonDP a) trs)
deriving instance Functor (Problem a    ) => Functor (Problem (NonDP a))
deriving instance NFData  (Problem a trs) => NFData  (Problem (NonDP a) trs)
deriving instance PprTPDB (Problem a trs) => PprTPDB (Problem (NonDP a) trs)
instance Observable1 NonDP
instance Observable a => Observable (NonDP a)
instance Observable1 (Problem a) => Observable1 (Problem (NonDP a))

-- Bogus instances (on purpose)

instance GetPairs (NonDP a) where getPairs typ trs = []
instance IsDPProblem a => IsDPProblem (NonDP a) where getP = getP . nonDPProblem
instance (MkDPProblem a trs) => MkDPProblem (NonDP a) trs where
  mkDPProblemO o (NonDP typ) rr pp = NonDPProblem (mkDPProblemO o typ rr pp)
  mapPO o f = NonDPProblem . mapPO o f . nonDPProblem
