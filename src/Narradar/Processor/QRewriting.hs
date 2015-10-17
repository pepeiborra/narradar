{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}
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
import Data.Foldable (toList)
import qualified Data.Set as Set
import qualified Data.Term.Family as Family
import Data.Typeable
import Narradar.Types
import Narradar.Types.Problem.QRewriting
import Narradar.Framework
import Prelude.Extras

import Debug.Hoed.Observe

-- | Transforms a Rewriting Problem into the Q-Rewriting problem with Q the empty set
data RewritingToQRewriting (info :: * -> *) = RewritingToQRewriting deriving Generic
instance Observable1 info => Observable (RewritingToQRewriting info)

data ReduceQ (info :: * -> *) = ReduceQ deriving Generic
instance Observable1 info => Observable (ReduceQ info)

type instance InfoConstraint (RewritingToQRewriting info) = info
data RewritingToQRewritingProof =
    RewritingToQRewritingProof
  | IRewritingToQRewritingProof
  deriving (Eq, Ord, Show, Generic, Typeable)

type instance InfoConstraint (ReduceQ info) = info
data ReduceQProof = ReduceQProof Int deriving (Eq, Ord, Show, Generic, Typeable)

instance Pretty RewritingToQRewritingProof where
    pPrint RewritingToQRewritingProof  = text "Considering a Q-Rewriting problem with Q empty"
    pPrint IRewritingToQRewritingProof = text "Considering a Q-Rewriting problem with Q = lhs(R)"

instance Pretty ReduceQProof where
    pPrint (ReduceQProof n) = text "Reduced the Q-set by" <+> n <+> text "terms"

instance Observable RewritingToQRewritingProof
instance Observable ReduceQProof

instance (FrameworkProblem Rewriting trs
         ,Info info RewritingToQRewritingProof
         ,MkDPProblem (QRewriting (Family.TermF trs)) trs
         ,Observable (Term(Family.TermF trs) Var)) =>
         Processor (RewritingToQRewriting info) (Problem Rewriting trs) where
  type Typ (RewritingToQRewriting info) (Problem Rewriting trs) = QRewriting (Family.TermF trs)
  type Trs (RewritingToQRewriting info) (Problem Rewriting trs) = trs
  applyO o RewritingToQRewriting p =
    singleP RewritingToQRewritingProof p $
     mapFramework (\(MkRewriting _ m) -> qRewritingO o mempty m) p

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


instance (Info info ReduceQProof
         ,FrameworkT t
         ,Ord1 t, Ord id
         ,NFData id
         ,id ~ Family.Id t
         ) =>
         Processor (ReduceQ info) (NarradarProblem (QRewriting t) t) where
  type Typ (ReduceQ info) (NarradarProblem (QRewriting t) t) = QRewriting t
  type Trs (ReduceQ info) (NarradarProblem (QRewriting t) t) = (NarradarTRS t Var)
  applyO o ReduceQ p@QRewritingProblem{q}
    | removed>0 = singleP (ReduceQProof removed) p p{q = qSetO o qset'}
    | otherwise  = mzero
   where
     sig = getDefinedSymbols p
     qset' = [ t | t <- toList(terms q), Just g <- [rootSymbol t], g `Set.member` sig ]
     removed = length (terms q) - length qset'
