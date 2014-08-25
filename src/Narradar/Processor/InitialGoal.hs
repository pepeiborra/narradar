{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, ConstraintKinds, MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies, KindSignatures #-}

module Narradar.Processor.InitialGoal where

import Data.Typeable
import GHC.Generics

import Narradar.Framework
import Narradar.Types

import Debug.Hoed.Observe

data LocalToGlobalP (info :: * -> *) = LocalToGlobalP deriving (Eq,Show,Ord,Typeable,Generic)
data LocalToGlobalProof = LocalToGlobalProof deriving (Eq,Show,Ord,Typeable,Generic)

type instance InfoConstraint (LocalToGlobalP info) = info

instance Observable (LocalToGlobalP info)
instance Observable (LocalToGlobalProof)

instance Pretty (LocalToGlobalProof) where
  pPrint _ = text "Global termination implies local termination"

instance Info info LocalToGlobalProof =>
         Processor (LocalToGlobalP info) (Problem (InitialGoal t base) trs) where
  type Typ (LocalToGlobalP info) (Problem (InitialGoal t base) trs) = base
  type Trs (LocalToGlobalP info) (Problem (InitialGoal t base) trs) = trs

  applyO _ LocalToGlobalP p = singleP LocalToGlobalProof p $ getBaseProblem p
