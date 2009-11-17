{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types.Problem.Relative where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import qualified Data.Set as Set

import Data.Term
import Data.Term.Rules

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils

data Relative trs p = Relative {relativeTRS_PType::trs, baseProblemType::p} deriving (Eq, Ord, Show)

instance IsProblem p => IsProblem (Relative trs0 p) where
  data Problem (Relative trs0 p) trs = RelativeProblem {relativeTRS::trs0, baseProblem::Problem p trs}
  getProblemType (RelativeProblem r0 p) = Relative r0 (getProblemType p)
  getR (RelativeProblem _ p) = getR p

instance IsDPProblem p => IsDPProblem (Relative trs0 p) where
  getP (RelativeProblem _ p) = getP p

instance MkProblem p trs => MkProblem (Relative trs p) trs where
  mkProblem (Relative r0 p) rr = RelativeProblem r0 (mkProblem p rr)
  mapR f (RelativeProblem r0 p) = RelativeProblem r0 (mapR f p)

instance MkDPProblem p trs => MkDPProblem (Relative trs p) trs where
  mapP f (RelativeProblem r0 p) = RelativeProblem r0 (mapP f p)
  mkDPProblem (Relative trs0 p) = (RelativeProblem trs0 .) . mkDPProblem p

instance FrameworkExtension (Relative id) where
  getBaseFramework = baseProblemType
  getBaseProblem   = baseProblem
  setBaseProblem p0 p = p{baseProblem=p0}

relative = Relative
relativeProblem = RelativeProblem

deriving instance (Eq trs, Eq (Problem p trs)) => Eq (Problem (Relative trs p) trs)
deriving instance (Ord trs, Ord (Problem p trs)) => Ord (Problem (Relative trs p) trs)
deriving instance (Show trs, Show (Problem p trs)) => Show (Problem (Relative trs p) trs)

instance Functor (Problem p) => Functor (Problem (Relative trs0 p)) where fmap f (RelativeProblem r0 p) = RelativeProblem r0 (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (Relative trs0 p)) where foldMap f (RelativeProblem r0 p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (Relative trs0 p)) where traverse f (RelativeProblem r0 p) = RelativeProblem r0 <$> traverse f p


$(derive makeFunctor     ''Relative)
$(derive makeFoldable    ''Relative)
$(derive makeTraversable ''Relative)


-- Data.Term instances


-- Output

instance Pretty p => Pretty (Relative trs p)
    where
         pPrint (Relative _ p) = text "Relative termination of" <+> pPrint p


instance (HasRules t v trs, Pretty (Term t v), Pretty (Problem base trs)) =>
    Pretty (Problem (Relative trs base) trs)
 where
  pPrint RelativeProblem{..} =
      pPrint baseProblem $$
      text "TRS':" <+> vcat [pPrint l <+> text "->=" <+> pPrint r
                              | l :-> r <- rules relativeTRS]
-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs')) =>
         ICap t v (Relative trs p, trs')
 where
         icap (Relative _ p,trs) = icap (p,trs)

-- Usable Rules

instance (Ord v, Ord (Term t v), IsTRS t v trs, Monoid trs, IsDPProblem typ, IUsableRules t v (typ, trs, trs)) =>
   IUsableRules t v (Relative trs typ, trs, trs)
    where
      iUsableRulesM (Relative r0 p, rr, dps) tt = do
            (_, usableRulesTRS, _) <- iUsableRulesM (p, r0 `mappend` rr, dps) tt
            let usableRulesSet = Set.fromList (rules usableRulesTRS :: [Rule t v])
                rr' = tRS $ toList (Set.fromList (rules rr) `Set.intersection` usableRulesSet)
                r0' = tRS $ toList (Set.fromList (rules r0) `Set.intersection` usableRulesSet)
            return (Relative r0' p,  rr', dps)
      iUsableRulesVarM (Relative r0 p, rr, dps) = iUsableRulesVarM (p, r0 `mappend` rr, dps)

{-
instance (Ord v, Ord (Term t v), IsTRS t v trs, IsTRS t v trs', IsDPProblem typ, IUsableRules t v (typ, [Rule t v], [Rule t v])) =>
   IUsableRules t v (Relative trs typ, trs', trs')
    where
      iUsableRulesM (Relative r0 p, rr, dps) tt = do
            (_, usableRulesTRS) <- iUsableRulesM (p, rules r0 `mappend` rules rr, dps) tt
            let usableRulesSet = Set.fromList (rules usableRulesTRS :: [Rule t v])
                rr' = tRS $ toList (Set.fromList (rules rr) `Set.intersection` usableRulesSet)
                r0' = tRS $ toList (Set.fromList (rules r0) `Set.intersection` usableRulesSet)
            return (Relative r0' p, rr', dps)
      iUsableRulesVarM (Relative r0 p, rr, dps) = iUsableRulesVarM (p, rules r0 `mappend` rules rr, dps)
-}


-- Insert Pairs

instance (MkDPProblem (Relative trs base) (NTRS id), InsertDPairs base (NTRS id)) => InsertDPairs (Relative trs base) (NTRS id) where
  insertDPairs RelativeProblem{..} newPairs = RelativeProblem{baseProblem = insertDPairs baseProblem newPairs, ..}
