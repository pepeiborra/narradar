{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Narradar.Processor.InnermostProblem where

import Data.Foldable (Foldable)

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types
import Narradar.Constraints.Syntactic

import qualified Data.Term.Family as Family

data ToInnermost (info :: * -> *) = ToInnermost
type instance InfoConstraint (ToInnermost info) = info

data ToInnermostProof = AlmostOrthogonalProof
                      | OrthogonalProof
                      | ToInnermostFail
         deriving (Eq, Ord, Show)

instance Pretty ToInnermostProof where
--   pPrint OverlayProof = text "R is an overlay system, therefore innermost termination implies termination"
   pPrint OrthogonalProof = text "R is orthogonal, therefore innermost termination implies termination"
   pPrint AlmostOrthogonalProof = text "R is almost orthogonal, therefore innermost termination implies termination"
   pPrint ToInnermostFail = text "Innermost termination does not imply termination for this system"

instance (HasRules trs
         ,Family.Rule trs ~ Rule t v
         ,v ~ Family.Var trs
         ,Ord v, Rename v, Enum v, Unify t
         ,Eq (t(Term t v))
         ,MkDPProblem IRewriting trs
         ,Info info ToInnermostProof
         ) =>
    Processor (ToInnermost info) (Problem Rewriting trs)
  where
   type Typ (ToInnermost info) (Problem Rewriting trs) = IRewriting
   type Trs (ToInnermost info) (Problem Rewriting trs) = trs
   apply ToInnermost p
      | isOrthogonal p = singleP OrthogonalProof p p'
      | isAlmostOrthogonal p = singleP AlmostOrthogonalProof p p'
--      | isOverlay && locallyConfluent = singleP OverlayProof p p'
      | otherwise = dontKnow ToInnermostFail p

    where
       p' = mkDerivedDPProblem (MkRewriting Innermost min) p
       cps = criticalPairs p
       MkRewriting st0 min = getFramework p

instance (HasRules trs
         ,Family.Rule trs ~ Rule t v
         ,v ~ Family.Var trs
         ,Ord v, Rename v, Enum v, Unify t
         ,Eq (t(Term t v))
         ,MkDPProblem IRewriting trs
         ,Info info ToInnermostProof
         ,Info info (Problem Rewriting trs)
         ,Info info (Problem IRewriting trs)
         ) =>
    Processor (ToInnermost info) (Problem (InitialGoal (TermF id) Rewriting) trs)
  where
   type Typ (ToInnermost info) (Problem (InitialGoal (TermF id) Rewriting) trs) = InitialGoal (TermF id) IRewriting
   type Trs (ToInnermost info) (Problem (InitialGoal (TermF id) Rewriting) trs) = trs
   apply ToInnermost = liftProcessor ToInnermost

-- instance (Info info (Problem base trs)
--          ,FrameworkExtension ext
--          ,Info info (Res (ToInnermost info) (Problem base trs))
--          ,Processor (ToInnermost info) (Problem base trs)
--          ) =>
--    Processor (ToInnermost info) (Problem (ext base) trs)
--   where
--     type Typ (ToInnermost info) (Problem (ext base) trs) = ext (Typ (ToInnermost info) (Problem base trs))
--     type Trs (ToInnermost info) (Problem (ext base) trs) = trs
--     apply = liftProcessor
