{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Narradar.Processor.InnermostProblem where

import Data.Foldable (Foldable)

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types
import Narradar.Constraints.Syntactic

data ToInnermost = ToInnermost
data ToInnermostProof = AlmostOrthogonalProof
                      | OrthogonalProof
                      | ToInnermostFail
         deriving (Eq, Ord, Show)

instance Pretty ToInnermostProof where
--   pPrint OverlayProof = text "R is an overlay system, therefore innermost termination implies termination"
   pPrint OrthogonalProof = text "R is orthogonal, therefore innermost termination implies termination"
   pPrint AlmostOrthogonalProof = text "R is almost orthogonal, therefore innermost termination implies termination"
   pPrint ToInnermostFail = text "Innermost termination does not imply termination for this system"

instance (HasRules t v trs, Ord v, Rename v, Enum v, Unify t
         ,Eq (t(Term t v))
         ,MkDPProblem IRewriting trs
         ,Info info ToInnermostProof) =>
    Processor info ToInnermost (Problem Rewriting trs) (Problem IRewriting trs)
  where
   apply ToInnermost p
      | isOrthogonal p = singleP OrthogonalProof p p'
      | isAlmostOrthogonal p = singleP AlmostOrthogonalProof p p'
--      | isOverlay && locallyConfluent = singleP OverlayProof p p'
      | otherwise = dontKnow ToInnermostFail p

    where
       p' = mkDerivedDPProblem (MkRewriting Innermost min) p
       cps = criticalPairs p
       MkRewriting st0 min = getFramework p

instance (Info info (Problem base trs)
         ,FrameworkExtension ext
         ,Info info (Problem base' trs)
         ,Processor info ToInnermost (Problem base trs) (Problem base' trs)) =>
   Processor info ToInnermost (Problem (ext base) trs) (Problem (ext base') trs)
  where
    apply = liftProcessor