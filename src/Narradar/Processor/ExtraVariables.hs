{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module Narradar.Processor.ExtraVariables where

import Control.Applicative
import Data.Foldable (Foldable)
import Data.Typeable

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe

data ExtraVarsP (info :: * -> *) = ExtraVarsP
type instance InfoConstraint (ExtraVarsP info) = info

--data ExtraVarsAF tag =  ExtraVarsAF (MkHeu tag)
data ExtraVarsProof = EVFail | EVAFFail deriving (Eq, Ord, Show, Generic, Typeable)

instance Observable (ExtraVarsP info) where observer = observeOpaque "Extra Vars"
instance Observable ExtraVarsProof

instance Pretty ExtraVarsProof where
    pPrint EVFail   = text "The TRS contains extra variables."
    pPrint EVAFFail = text "Failed to find an argument filtering which filters out the extra variables"


instance (QRewritingConstraint t, ExtraVars trs, Ord(Family.Var trs), Info info ExtraVarsProof) =>
          Processor (ExtraVarsP info) (Problem (QRewriting t) trs)
  where
    type Typ (ExtraVarsP info) (Problem (QRewriting t) trs) = QRewriting t
    type Trs (ExtraVarsP info) (Problem (QRewriting t) trs) = trs
    applyO _ _ p
       | null (extraVars p) = return p
       | otherwise  = refuted EVFail p

instance (ExtraVars trs, Ord (Family.Var trs), Info info ExtraVarsProof) =>
          Processor (ExtraVarsP info) (Problem Rewriting trs)
  where
    type Typ (ExtraVarsP info) (Problem Rewriting trs) = Rewriting
    type Trs (ExtraVarsP info) (Problem Rewriting trs) = trs
    applyO _ _ p
       | null (extraVars p) = return p
       | otherwise  = refuted EVFail p


instance (ExtraVars trs, Ord (Family.Var trs), Info info ExtraVarsProof) =>
          Processor (ExtraVarsP info) (Problem IRewriting trs)
  where
    type Typ (ExtraVarsP info) (Problem IRewriting trs) = IRewriting
    type Trs (ExtraVarsP info) (Problem IRewriting trs) = trs
    applyO _ _ p
       | null (extraVars p) = return p
       | otherwise  = refuted EVFail p


instance ( Processor (ExtraVarsP info) (Problem base trs)
         , trs ~ Trs (ExtraVarsP info) (Problem base trs)
         , Ord (Family.Var trs)
         , Info info ExtraVarsProof
         , Info info (Problem base  trs)
         , Info info (Res (ExtraVarsP info) (Problem base trs))
         ) =>
          Processor (ExtraVarsP info) (Problem (InitialGoal t base) trs)
  where
    type Typ (ExtraVarsP info) (Problem (InitialGoal t base) trs) = InitialGoal t (Typ (ExtraVarsP info) (Problem base trs))
    type Trs (ExtraVarsP info) (Problem (InitialGoal t base) trs) = trs

    applyO o tag@ExtraVarsP p = (`setBaseProblem` p) <$> applyO o tag (getBaseProblem p)


instance ( Processor (ExtraVarsP info) (Problem base trs)
         , trs ~ Trs (ExtraVarsP info) (Problem base trs)
         , Info info ExtraVarsProof
         , Info info (Problem base  trs)
         , Info info (Res (ExtraVarsP info) (Problem base trs))
         ) =>
          Processor (ExtraVarsP info) (Problem (Relative trs base) trs)
  where
    type Typ (ExtraVarsP info) (Problem (Relative trs base) trs) = Relative trs (Typ (ExtraVarsP info) (Problem base trs))
    type Trs (ExtraVarsP info) (Problem (Relative trs base) trs) = trs

    applyO o tag@ExtraVarsP p = (`setBaseProblem` p) <$> applyO o tag (getBaseProblem p)


-- In this case we don't need to do anything since Narrowing can terminate with extra variables
instance Info info ExtraVarsProof
       => Processor (ExtraVarsP info) (Problem (MkNarrowingGoal id p) trs)
  where
    type Typ (ExtraVarsP info) (Problem (MkNarrowingGoal id p) trs) = MkNarrowingGoal id p
    type Trs (ExtraVarsP info) (Problem (MkNarrowingGoal id p) trs) = trs
    applyO _ ExtraVarsP = return

instance (ExtraVars trs, Info info ExtraVarsProof) =>
         Processor (ExtraVarsP info) (Problem (MkNarrowing a) trs) where
    type Typ (ExtraVarsP info) (Problem (MkNarrowing a) trs) = MkNarrowing a
    type Trs (ExtraVarsP info) (Problem (MkNarrowing a) trs) = trs
    applyO _ ExtraVarsP = return

{-
instance Processor (ExtraVarsAF tag) (NarrowingGoal id p) (NarrowingGoal id p)
    applySearch (ExtraVarsAF mkH) p
       | null vv = return p
       | null orProblems    = failP EVAFFail p
       | otherwise          = orProblems
     where
       vv  = extraVars p
       heu = mkHeu mkH p
-}
