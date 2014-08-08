{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}

module Narradar.Types.Problem.Relative where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import qualified Data.Set as Set
import Data.Typeable

import Data.Term hiding (TermF)
import Data.Term.Rules
import qualified Data.Term.Family as Family

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

import Debug.Hoed.Observe

data Relative trs p = Relative {relativeTRS_PType::trs, baseFramework::p} deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable)

--instance GetPairs p => GetPairs (Relative trs p) where getPairs = getPairs . baseProblem

instance IsProblem p => IsProblem (Relative trs0 p) where
  data Problem (Relative trs0 p) trs = RelativeProblem {relativeTRS::trs0, baseProblem::Problem p trs} deriving Generic
  getFramework (RelativeProblem r0 p) = Relative r0 (getFramework p)
  getR (RelativeProblem _ p) = getR p

instance (Observable trs, Observable1 (Problem p)) => Observable1 (Problem (Relative trs p))

instance IsDPProblem p => IsDPProblem (Relative trs0 p) where
  getP (RelativeProblem _ p) = getP p

instance (Monoid trs, MkProblem p trs) => MkProblem (Relative trs p) trs where
  mkProblem (Relative r0 p) rr = RelativeProblem r0 $ mkProblem p (rr `mappend` r0)
  mapRO o f (RelativeProblem r0 p) = RelativeProblem r0 (mapRO o f p)

--instance (Monoid trs, MkDPProblem p trs) => MkDPProblem (Relative trs p) trs where
instance (FrameworkN p t v) =>
    MkDPProblem (Relative (NarradarTRS t v) p) (NarradarTRS t v)
 where
  mapPO o f (RelativeProblem r0 p) = RelativeProblem r0 (mapPO o f p)
  mkDPProblemO o (Relative trs0 p) rr dps = RelativeProblem trs0 $
                                             mkDPProblemO o p (rr `mappend` trs0) dps

instance FrameworkExtension (Relative id) where
  getBaseFramework  = baseFramework
  getBaseProblem    = baseProblem
  liftFramework f (Relative trs0 p) = Relative trs0 (f p)
  liftProblem   f p = f (baseProblem p) >>= \p0' -> return p{baseProblem = p0'}
  liftProcessorS = liftProcessorSdefault

relative = Relative
relativeProblem = RelativeProblem

deriving instance (Eq trs, Eq (Problem p trs)) => Eq (Problem (Relative trs p) trs)
deriving instance (Ord trs, Ord (Problem p trs)) => Ord (Problem (Relative trs p) trs)
deriving instance (Show trs, Show (Problem p trs)) => Show (Problem (Relative trs p) trs)

instance Functor (Problem p) => Functor (Problem (Relative trs0 p)) where fmap f (RelativeProblem r0 p) = RelativeProblem r0 (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (Relative trs0 p)) where foldMap f (RelativeProblem r0 p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (Relative trs0 p)) where traverse f (RelativeProblem r0 p) = RelativeProblem r0 <$> traverse f p



-- Output

instance Pretty p => Pretty (Relative trs p)
    where
         pPrint (Relative _ p) = text "Relative termination of" <+> pPrint p


instance ( FrameworkN base t v
         ) =>
    Pretty (Problem (Relative (NarradarTRS t v) base) (NarradarTRS t v))
 where
  pPrint RelativeProblem{..}
    = pPrint p0' $$
      text "TRS':" <+> vcat [pPrint l <+> text "->=" <+> pPrint r
                               | l :-> r <- rules relativeTRS]
   where
      p0' = mapR (filterNarradarTRS (`Set.notMember` narradarTRStoSet relativeTRS)) baseProblem

instance ( IsTRS trs
         , v ~ Family.Var trs
         , t ~ Family.TermF trs
         , Rule t v ~ Family.Rule trs
         , MkProblem base trs
         , Pretty (t(Term t v))
         , Ord (Term t v)
         , HasId1 t, Functor t, Foldable t, Pretty (Family.Id t)
         , PprTPDB v
         , PprTPDB (Problem base trs)
         ) => PprTPDB (Problem (Relative trs base) trs) where
  pprTPDB RelativeProblem{..} =
      pprTPDB p0' $$
      parens(text "RULES" $$
             nest 1 (vcat [ pprTPDB l <+> text "->=" <+> pprTPDB r
                            | l :-> r <- rules relativeTRS]))
   where
      p0' = mapR ( tRS . Set.toList
                 . (`Set.difference` Set.fromList (rules relativeTRS))
                 . Set.fromList . rules)
                 baseProblem

-- ICap

instance (HasRules trs, Unify (TermF trs), GetVars trs, ICap (Problem p trs')) =>
         ICap (Problem (Relative trs p) trs')
 where
         icapO = liftIcapO

-- Usable Rules
instance (Monoid trs, IsProblem b, IUsableRules (Problem b trs)
         ,FrameworkProblem (Relative trs b) trs
         ) => IUsableRules (Problem (Relative trs b) trs) where
  iUsableRulesM p _ _ = return p
  iUsableRulesVarM    = liftUsableRulesVarM
{-
instance (Ord v, Ord (Term t v), IsTRS t v trs, Monoid trs, IsDPProblem typ, IUsableRules t v typ trs) =>
   IUsableRules t v (Relative trs typ) trs
    where
      iUsableRulesM (Relative r0 p) rr dps tt = do
            (_, usableRulesTRS, _) <- iUsableRulesM (p, r0 `mappend` rr, dps) tt
            let usableRulesSet = Set.fromList (rules usableRulesTRS :: [Rule t v])
                rr' = tRS $ toList (Set.fromList (rules rr) `Set.intersection` usableRulesSet)
                r0' = tRS $ toList (Set.fromList (rules r0) `Set.intersection` usableRulesSet)
            return (Relative r0' p,  rr', dps)
      iUsableRulesVarM (Relative r0 p) rr = iUsableRulesVarM p (r0 `mappend` rr)
-}

-- Insert Pairs

instance (MkDPProblem (Relative trs base) (NTRS id), InsertDPairs base (NTRS id)) => InsertDPairs (Relative trs base) (NTRS id) where
  insertDPairs RelativeProblem{..} newPairs = RelativeProblem{baseProblem = insertDPairs baseProblem newPairs, ..}
