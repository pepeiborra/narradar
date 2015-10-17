{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module Narradar.Processor.NonDP (ToDP(..), NoRules(..)) where

import Control.Monad (mzero)
import Data.List ((\\), partition)
import Data.Monoid
import Data.Typeable
import Prelude.Extras
import qualified Data.Set as Set

import Narradar.Constraints.Modularity
import Narradar.Constraints.Syntactic
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types hiding (goals)
import Narradar.Types.Problem.NonDP

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe

-- ----------------------------------------------------------
-- A Processor for converting NonDP problems into DP problems
-- ----------------------------------------------------------

data ToDP (info :: (* -> *)) = ToDP
type instance InfoConstraint (ToDP info) = info
data ToDPProof = ToDPProof deriving (Eq, Ord, Show, Typeable, Generic)

instance Observable ToDPProof

instance Pretty ToDPProof where pPrint _ = text "Termination of the DP problem implies termination of the TRS"

instance (GetPairs a
         ,Info info ToDPProof
         ,trs ~ NTRS (DPIdentifier id)
         ,MkDPProblem a trs
         ,FrameworkId id
         ) => Processor (ToDP info) (Problem (NonDP a) trs) where
  type Typ (ToDP info) (Problem (NonDP a) trs) = a
  type Trs (ToDP info) (Problem (NonDP a) trs) = trs

  applyO oo ToDP p = singleP ToDPProof p $
                     mkDPProblemO oo typ (getR p) (tRS $ getPairs typ (getR p))
     where
       NonDP typ = getFramework p

-- --------------------------------------------------------
-- A Processor for eliminating NonDP problems with no rules
-- --------------------------------------------------------

data NoRules (info :: (* -> *)) = NoRules
type instance InfoConstraint (NoRules info) = info
data NoRulesProof = NoRulesProof deriving (Eq,Ord,Show,Typeable,Generic)
instance Observable NoRulesProof
instance Pretty NoRulesProof where pPrint _ = text "Trivially terminating (no rules)"

instance (Info info NoRulesProof, IsProblem a, HasRules trs
         ) => Processor (NoRules info) (Problem (NonDP a) trs) where
  type Typ (NoRules info) (Problem (NonDP a) trs) = NonDP a
  type Trs (NoRules info) (Problem (NonDP a) trs) = trs
  applyO oo NoRules p =
    if null (rules $ getR p)
      then success NoRulesProof p
      else mzero
