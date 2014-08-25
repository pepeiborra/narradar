{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module Narradar.Processor.QRewriting where

import Control.Applicative
import Control.DeepSeq
import Data.List ((\\))
import Control.Monad
import Data.Monoid
import qualified Data.Term.Family as Family
import Data.Typeable
import Narradar.Types
import Narradar.Framework

import Debug.Hoed.Observe

-- | Transforms a Rewriting Problem into the Q-Rewriting problem with Q the empty set
data RewritingToQRewriting (info :: * -> *) = RewritingToQRewriting deriving Generic
instance Observable1 info => Observable (RewritingToQRewriting info)

type instance InfoConstraint (RewritingToQRewriting info) = info
data RewritingToQRewritingProof =
    RewritingToQRewritingProof
  | IRewritingToQRewritingProof
  deriving (Eq, Ord, Show, Generic, Typeable)

instance Pretty RewritingToQRewritingProof where
    pPrint RewritingToQRewritingProof  = text "Considering a Q-Rewriting problem with Q empty"
    pPrint IRewritingToQRewritingProof = text "Considering a Q-Rewriting problem with Q = lhs(R)"

instance Observable RewritingToQRewritingProof

instance (FrameworkProblem Rewriting trs
         ,Info info RewritingToQRewritingProof
         ,MkDPProblem (QRewriting (Family.TermF trs)) trs) =>
         Processor (RewritingToQRewriting info) (Problem Rewriting trs) where
  type Typ (RewritingToQRewriting info) (Problem Rewriting trs) = QRewriting (Family.TermF trs)
  type Trs (RewritingToQRewriting info) (Problem Rewriting trs) = trs
  applyO _ RewritingToQRewriting p =
    singleP RewritingToQRewritingProof p $ mapFramework (\_ -> qrewriting) p

instance (FrameworkN IRewriting t Var
         ,Info info RewritingToQRewritingProof
         ) =>
         Processor (RewritingToQRewriting info) (NarradarProblem IRewriting t) where
  type Typ (RewritingToQRewriting info) (NarradarProblem IRewriting t) = QRewriting t
  type Trs (RewritingToQRewriting info) (NarradarProblem IRewriting t) = NarradarTRS t Var
  applyO (O o oo) RewritingToQRewriting p =
    singleP IRewritingToQRewritingProof p $
    oo "mapFramework" mapFrameworkO (\m -> qRewritingO (O o oo) (lhs <$> rules(getR p)) (getMinimality m)) p

instance (FrameworkProblem Rewriting trs
         ,Info info RewritingToQRewritingProof
         ,Info info (Problem (QRewriting t) trs)
         ,Info info (Problem Rewriting trs)
         ,t ~ Family.TermF trs
         ,v ~ Family.Var trs
         ,MkDPProblem (QRewriting t) trs
         ) =>
         Processor (RewritingToQRewriting info) (Problem (InitialGoal t Rewriting) trs) where
  type Typ (RewritingToQRewriting info) (Problem (InitialGoal t Rewriting) trs) =
    InitialGoal t (QRewriting t)
  type Trs (RewritingToQRewriting info) (Problem (InitialGoal t Rewriting) trs) = trs
  applyO o RewritingToQRewriting = liftProcessor o RewritingToQRewriting

