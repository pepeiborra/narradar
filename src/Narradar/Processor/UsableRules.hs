{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module Narradar.Processor.UsableRules where

import Control.Monad
import Data.List ((\\))
import Data.Monoid
import Data.Typeable
import qualified Data.Term.Family as Family

import Narradar.Types
import Narradar.Types.Problem.QRewriting
import Narradar.Framework
import Narradar.Framework.Ppr

import Debug.Hoed.Observe

data UsableRules (info :: * -> *) = UsableRules deriving (Generic, Typeable)
instance Observable1 info => Observable (UsableRules info)
type instance InfoConstraint (UsableRules info) = info
data UsableRulesProof term = UsableRulesProof [RuleF term]
                           | QUsableRulesProof [RuleF term]
                           deriving (Eq, Ord, Show, Generic1, Typeable)


usableRulesProof p p' = singleP (UsableRulesProof (rules(getR p) \\ rules(getR p'))) p p'
qusableRulesProof p p' = singleP (UsableRulesProof (rules(getR p) \\ rules(getR p'))) p p'

instance Pretty term => Pretty (UsableRulesProof term) where
  pPrint (UsableRulesProof rr)  =
    text "By Theorem 3.26 in [Rene Thiemann's thesis], we can remove the following rules from R:" $$
    nest 2 (vcat (map pPrint rr))

instance Observable1 UsableRulesProof
instance Observable a => Observable (UsableRulesProof a) where
  observer = observer1 ; observers = observers1

instance (Info info (UsableRulesProof (Term t Var))
         ,FrameworkN (QRewriting t) t Var
         ) => Processor (UsableRules info) (NarradarProblem (QRewriting t) t) where
  type Typ (UsableRules info) (NarradarProblem (QRewriting t) t) = QRewriting t
  type Trs (UsableRules info) (NarradarProblem (QRewriting t) t) = NarradarTRS t Var
  applyO obs@(O _ oo) UsableRules p
   | length(rules $ getR p') == length(rules $ getR p) = mzero
   | otherwise = qusableRulesProof p p'
   where
    rr' = getR $ oo "iUsableRulesO" iUsableRulesO p
    -- Avoid a call to setR, which would recompute the DP unifiers, as it is not needed
    p' = p{ rr = rr', qCondition = mkQConditionO obs (q p) rr'}
