{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.Processor.UsableRules where

import Data.List ((\\))
import Control.Monad
import Data.Monoid
import qualified Data.Term.Family as Family

import Narradar.Types
import Narradar.Framework
import Narradar.Framework.Ppr

data UsableRules (info :: * -> *) = UsableRules
type instance InfoConstraint (UsableRules info) = info
data UsableRulesProof term = UsableRulesProof [RuleF term]
                           | QUsableRulesProof [RuleF term]
                           deriving (Eq, Ord, Show)

usableRulesProof p p' = singleP (UsableRulesProof (rules(getR p) \\ rules(getR p'))) p p'
qusableRulesProof p p' = singleP (UsableRulesProof (rules(getR p) \\ rules(getR p'))) p p'

instance Pretty term => Pretty (UsableRulesProof term) where
  pPrint (UsableRulesProof rr)  =
    text "By Theorem 3.26 in [Rene Thiemann's thesis], we can remove the following rules from R:" $$
    nest 2 (vcat (map pPrint rr))

instance (Info info (UsableRulesProof term)
         ,term ~ Term (Family.TermF trs) (Family.Var trs)
         ,Family.Rule trs ~ Rule (Family.TermF trs) (Family.Var trs)
         ,FrameworkProblem (QRewriting term) trs
         ,Eq trs
         ) => Processor (UsableRules info) (Problem (QRewriting term) trs) where
  type Typ (UsableRules info) (Problem (QRewriting term) trs) = QRewriting term
  type Trs (UsableRules info) (Problem (QRewriting term) trs) = trs
  apply UsableRules p
   | p' == p = mzero
   | otherwise = qusableRulesProof p p'
   where
    p' = iUsableRules p
