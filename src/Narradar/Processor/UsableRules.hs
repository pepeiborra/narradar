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
                           deriving (Eq, Ord, Show, Generic, Typeable)


usableRulesProof p p' = singleP (UsableRulesProof (rules(getR p) \\ rules(getR p'))) p p'
qusableRulesProof p p' = singleP (UsableRulesProof (rules(getR p) \\ rules(getR p'))) p p'

instance Pretty term => Pretty (UsableRulesProof term) where
  pPrint (UsableRulesProof rr)  =
    text "By Theorem 3.26 in [Rene Thiemann's thesis], we can remove the following rules from R:" $$
    nest 2 (vcat (map pPrint rr))

instance Observable1 UsableRulesProof

instance (Info info (UsableRulesProof term)
         ,term ~ Term (Family.TermF trs) (Family.Var trs)
         ,Family.Rule trs ~ Rule (Family.TermF trs) (Family.Var trs)
         ,FrameworkProblem (QRewriting term) trs
         ,Eq trs, Pretty trs
         ) => Processor (UsableRules info) (Problem (QRewriting term) trs) where
  type Typ (UsableRules info) (Problem (QRewriting term) trs) = QRewriting term
  type Trs (UsableRules info) (Problem (QRewriting term) trs) = trs
  applyO (O _ oo) UsableRules p
   | length(rules $ getR p') == length(rules $ getR p) = mzero
   | otherwise = qusableRulesProof p p'
   where
    rr' = getR $ oo "iUsableRulesO" iUsableRulesO p
    -- Avoid a call to setR, which would recompute the DP unifiers, as it is not needed
    p' = p{ rr = rr', qCondition = mkQCondition (q p) rr'}
