{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Narradar.Processor.QRewriting where

import Control.Applicative
import Data.List ((\\))
import Control.Monad
import Data.Monoid
import qualified Data.Term.Family as Family
import Narradar.Types
import Narradar.Framework

import Debug.Hoed.Observe

-- | Transforms a Rewriting Problem into the Q-Rewriting problem with Q the empty set
data RewritingToQRewriting (info :: * -> *) = RewritingToQRewriting
type instance InfoConstraint (RewritingToQRewriting info) = info
data RewritingToQRewritingProof =
    RewritingToQRewritingProof
  | IRewritingToQRewritingProof
  deriving (Eq, Ord, Show)

instance Pretty RewritingToQRewritingProof where
    pPrint RewritingToQRewritingProof  = text "Considering a Q-Rewriting problem with Q empty"
    pPrint IRewritingToQRewritingProof = text "Considering a Q-Rewriting problem with Q = lhs(R)"

instance (FrameworkProblem Rewriting trs
         ,Info info RewritingToQRewritingProof
         ,MkDPProblem (QRewriting (TermFor trs)) trs) =>
         Processor (RewritingToQRewriting info) (Problem Rewriting trs) where
  type Typ (RewritingToQRewriting info) (Problem Rewriting trs) = QRewriting (TermFor trs)
  type Trs (RewritingToQRewriting info) (Problem Rewriting trs) = trs
  apply RewritingToQRewriting p =
    singleP RewritingToQRewritingProof p $ mapFramework (\_ -> qrewriting) p

instance (FrameworkProblem IRewriting trs
         ,Info info RewritingToQRewritingProof
         ,MkDPProblem (QRewriting (TermFor trs)) trs
         ,Family.Rule trs ~ Rule (Family.TermF trs) (Family.Var trs)
         ) =>
         Processor (RewritingToQRewriting info) (Problem IRewriting trs) where
  type Typ (RewritingToQRewriting info) (Problem IRewriting trs) = QRewriting (TermFor trs)
  type Trs (RewritingToQRewriting info) (Problem IRewriting trs) = trs
  apply RewritingToQRewriting p =
    singleP IRewritingToQRewritingProof p $
    mapFramework (\m -> QRewriting (QSet $ lhs <$> rules(getR p)) (getMinimality m)) p

instance (FrameworkProblem Rewriting trs
         ,Info info RewritingToQRewritingProof
         ,Info info (Problem (QRewriting (Term t v)) trs)
         ,Info info (Problem Rewriting trs)
         ,t ~ Family.TermF trs
         ,v ~ Family.Var trs
         ,MkDPProblem (QRewriting (Term t v)) trs
         ) =>
         Processor (RewritingToQRewriting info) (Problem (InitialGoal t Rewriting) trs) where
  type Typ (RewritingToQRewriting info) (Problem (InitialGoal t Rewriting) trs) =
    InitialGoal t (QRewriting (Term t (Family.Var trs)))
  type Trs (RewritingToQRewriting info) (Problem (InitialGoal t Rewriting) trs) = trs
  apply RewritingToQRewriting = liftProcessor RewritingToQRewriting

