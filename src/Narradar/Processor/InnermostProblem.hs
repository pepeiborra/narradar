{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Narradar.Processor.InnermostProblem (ToInnermost(..)) where

import Control.Applicative

import Control.DeepSeq
import Data.Foldable (Foldable)
import Data.List (find, (\\))
import Data.Maybe (isNothing)
import Data.Monoid
--import Data.Term (Match, Rename, variant, isRenaming, match)
import Data.Term.Narrowing (isRNF)
import Data.Term.Rewriting (rewrites)

import qualified Data.Map as Map
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Types
import Narradar.Constraints.Confluence

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe as Hood

data ToInnermost (info :: * -> *) = ToInnermost
type instance InfoConstraint (ToInnermost info) = info

data ToInnermostProof = AlmostOrthogonalProof
                      | OrthogonalProof
                      | OverlayProof
                      | QInnermostProof
                      | ToInnermostFail
                      | QInnermostFail String
         deriving (Eq, Ord, Show)

instance Pretty ToInnermostProof where
   pPrint OverlayProof = text "R is an overlay system, therefore innermost termination implies termination"
   pPrint OrthogonalProof = text "R is orthogonal, therefore innermost termination implies termination"
   pPrint AlmostOrthogonalProof = text "R is almost orthogonal, therefore innermost termination implies termination"
   pPrint ToInnermostFail = text "Innermost termination does not imply termination for this system"
   pPrint QInnermostProof = text "By theorem 3.14 in [RThiemannThe], Q = lhs(R) "
   pPrint (QInnermostFail reason) = text "Cannot apply theorem 3.14 from [RThiemannThe] because:\n  " <+> text reason

-- | This processor cannot be applied after we have substracted rules from R.
--   FIXME: Recast it as a non-DP problem processor only
instance (HasRules trs
         ,Family.Rule trs ~ Rule t v
         ,v ~ Family.Var trs
         ,Ord v, Rename v, Enum v, Unify t
         ,Ord (Term t v)
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
      | isOverlayTRS p && locallyConfluent p = singleP OverlayProof p p'
      | otherwise = dontKnow ToInnermostFail p

    where
       p' = mkDerivedDPProblem (MkRewriting Innermost min) p
       cps = criticalPairs p
       MkRewriting st0 min = getFramework p

-- | FIXME This processor cannot be applied after we have substracted rules from R.
--   FIXME: Recast it as a non-DP problem processor only
instance (HasRules trs
         ,Family.Rule trs ~ Rule t v
         ,v ~ Family.Var trs
         ,Ord v, Rename v, Enum v, Unify t
         ,Ord(Term t v)
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


-- Implementation of Theorem 3.14 in Rene Thiemann's thesis
instance (Family.Rule trs ~ Rule t v
         ,v ~ Family.Var trs
         ,Info info ToInnermostProof
         ,FrameworkProblem (QRewriting (Term t v)) trs
         ,FrameworkN (QRewriting (Term t v)) t v
         ,Eq trs
         ) =>
    Processor (ToInnermost info) (Problem (QRewriting (Term t v)) trs)
  where
   type Typ (ToInnermost info) (Problem (QRewriting (Term t v)) trs) = QRewriting (Term t v)
   type Trs (ToInnermost info) (Problem (QRewriting (Term t v)) trs) = trs
   apply ToInnermost p
      | isNothing cond1 && isNothing cond2 && cond3 && cond4 && p' /= p = singleP QInnermostProof p p'
      | otherwise = dontKnow (QInnermostFail reason) p

    where
       cond1 = find (not . isRNF r) (lhs <$> rules(getP p))
       cond2
        | null q    = find (\(_,s,t) -> not({-gdmobserve "joinable"-} joinable s t))
                           ({-gdmobserve "criticalPairs"-} criticalPairs r)
        | otherwise = find (\(_,s,t) -> not(s == t)) (criticalPairs r)
       cond3 = isQValid p
       cond4 = m == M
       r  = rules(getR p)
       p' = mkDerivedDPProblem (QRewriting (QSet (lhs <$> r)) m) p
       joinable s t =
            last (take 100 (rewrites r s)) == last(take 100 (rewrites r t))

       QRewriting (QSet q) m = getFramework p

       reason =
         case (cond1, cond2, cond3, cond4) of
          (Just t,_,_,_) -> "a subterm of " ++ show(pPrint t) ++ " unifies with a lhs of R"
          (_,Just (_,a,b),_,_) | null q -> "critical pair " ++ show(pPrint (a,b)) ++ " may not be joinable"
          (_,Just (_,a,b),_,_)  -> "critical pair " ++ show(pPrint (a,b)) ++ " is not trivial"
          (_,_,False,_) -> "NF(R) \\notsubseteq NF(Q)"
          (_,_,_,False) -> "lack of minimality"

-- Adaptation of Theorem 3.14 in Rene's thesis
instance (Family.Rule trs ~ Rule t v
         ,v ~ Family.Var trs
         ,Info info ToInnermostProof
         ,Info info (Problem (QRewriting (Term t v)) trs)
         ,FrameworkN (InitialGoal (TermF id) (QRewriting (Term t v))) t v
         ,FrameworkN (QRewriting (Term t v)) t v
         ,FrameworkProblem (InitialGoal (TermF id) (QRewriting (Term t v))) trs
         ,FrameworkProblem (QRewriting (Term t v)) trs
         ,Eq trs
         ) =>
    Processor (ToInnermost info) (Problem (InitialGoal (TermF id) (QRewriting (Term t v))) trs)
  where
   type Typ (ToInnermost info) (Problem (InitialGoal (TermF id) (QRewriting (Term t v))) trs) = InitialGoal (TermF id) (QRewriting (Term t v))
   type Trs (ToInnermost info) (Problem (InitialGoal (TermF id) (QRewriting (Term t v))) trs) = trs
   apply ToInnermost = liftProcessor ToInnermost
