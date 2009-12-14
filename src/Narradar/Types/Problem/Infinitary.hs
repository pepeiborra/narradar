{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Narradar.Types.Problem.Infinitary where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM, fmapDefault, foldMapDefault)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Text.XHtml (theclass)

import Data.Term
import Data.Term.Rules

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..), PolyHeuristic, MkHeu, mkHeu, bestHeu, fromAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Term
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils (chunks)

import Prelude hiding (pi)


data Infinitary id p = forall heu . PolyHeuristic heu id => Infinitary {pi_PType :: AF_ id, heuristic :: MkHeu heu , baseProblemType :: p}

instance (Ord id, IsProblem p) => IsProblem (Infinitary id p)  where
  data Problem (Infinitary id p) a = InfinitaryProblem {pi::AF_ id, baseProblem::Problem p a}
  getProblemType (InfinitaryProblem af p) = infinitary' af (getProblemType p)
  getR   (InfinitaryProblem _ p) = getR p

instance (Ord id, IsDPProblem p, MkProblem p trs, HasSignature trs, id ~ SignatureId (Problem p trs)) =>
    MkProblem (Infinitary id p) trs where
  mkProblem (Infinitary af _ base) rr = InfinitaryProblem (af `mappend` AF.init p) p where p = mkProblem base rr
  mapR f (InfinitaryProblem af p) = InfinitaryProblem af (mapR f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (Infinitary id p) where
  getP   (InfinitaryProblem _  p) = getP p

instance (id ~ SignatureId (Problem p trs), HasSignature trs, Ord id, MkDPProblem p trs) =>
    MkDPProblem (Infinitary id p) trs where
  mapP f (InfinitaryProblem af p) = InfinitaryProblem af (mapP f p)
  mkDPProblem (Infinitary af _ base) rr dp = InfinitaryProblem (af `mappend` AF.init p) p
    where p = mkDPProblem base rr dp

infinitary  g p = Infinitary (mkGoalAF g) bestHeu p
infinitary' g p = Infinitary g bestHeu p

mkDerivedInfinitaryProblem g mkH p = do
  let heu = mkHeu mkH p
      af  = mkGoalAF g `mappend` AF.init p
  af' <-  Set.toList $ invariantEV heu p af
  let p' = InfinitaryProblem af' p --  $ (iUsableRules p (rhs <$> rules (getP p)))
  return p'

-- Eq,Ord,Show
deriving instance (Eq id, Eq (Problem p trs)) => Eq (Problem (Infinitary id p) trs)
deriving instance (Ord id, Ord (Problem p trs)) => Ord (Problem (Infinitary id p) trs)
deriving instance (Show id, Show (Problem p trs)) => Show (Problem (Infinitary id p) trs)

-- Functor
{-
instance Functor (Infinitary id) where fmap = fmapDefault
instance Foldable (Infinitary id) where foldMap = foldMapDefault
instance Traversable (Infinitary id) where traverse f (Infinitary pi heu p) = Infinitary pi heu <$> f p
-}

instance Functor (Problem p) => Functor (Problem (Infinitary id p)) where fmap f (InfinitaryProblem af p) = InfinitaryProblem af (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (Infinitary id p)) where foldMap f (InfinitaryProblem af p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (Infinitary id p)) where traverse f (InfinitaryProblem af p) = InfinitaryProblem af <$> traverse f p

-- Data.Term instances

-- Output

instance Pretty p => Pretty (Infinitary id p) where
    pPrint Infinitary{..} = text "Infinitary" <+> pPrint baseProblemType

instance HTMLClass (Infinitary id Rewriting) where htmlClass _ = theclass "InfRew"
instance HTMLClass (Infinitary id IRewriting) where htmlClass _ = theclass "InfIRew"
instance HTMLClass (Infinitary id Narrowing) where htmlClass _ = theclass "InfNarr"
instance HTMLClass (Infinitary id CNarrowing) where htmlClass _ = theclass "InfCNarr"


instance (Pretty id, PprTPDB (Problem typ trs)) =>
  PprTPDB (Problem (Infinitary id typ) trs)
 where
   pprTPDB (InfinitaryProblem pi p) =
      pprTPDB p $$
      parens(text "AF" <+> pprAF pi)


pprAF af = vcat [ hsep (punctuate comma [ pPrint f <> colon <+> either (pPrint.id) (pPrint.toList) aa | (f, aa) <- xx])
                      | xx <- chunks 3 $ Map.toList $ fromAF af]

-- Icap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (Infinitary id p, trs)
  where
    icap (Infinitary{..},trs) = icap (baseProblemType,trs)

-- Usable Rules

instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v), ApplyAF trs
         , id ~ AFId trs, AFId (Term t v) ~ id, Ord id, Ord (t(Term t v))
         ,IUsableRules t v p trs, ICap t v (p,trs)) =>
   IUsableRules t v (Infinitary id p) trs
 where
   iUsableRulesM Infinitary{..} trs dps tt = do
      pi_tt <- getFresh (AF.apply pi_PType tt)
      let it = (baseProblemType, trs)
      trs'  <- f_UsableRulesAF it pi_PType (iUsableRulesVarM baseProblemType trs dps) pi_tt
      return (tRS $ rules trs')

   iUsableRulesVarM Infinitary{..} = iUsableRulesVarM baseProblemType

{-
instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v), ApplyAF trs
         , id ~ AFId trs, AFId (Term t v) ~ id, Ord id, Ord (t(Term t v))
         ,IUsableRules t v (p, trs, trs), ICap t v (p,trs)) =>
   IUsableRules t v (Infinitary id p, trs, trs)
 where
   iUsableRulesM p@(typ@Infinitary{..}, trs, dps) tt = do
      pi_tt <- getFresh (AF.apply pi_PType tt)
      trs'  <- f_UsableRulesAF (baseProblemType, trs) pi_PType (iUsableRulesVarM p) pi_tt
      return (typ, tRS $ rules trs', dps)

   iUsableRulesVarM (Infinitary{..},trs) = iUsableRulesVarM (baseProblemType, trs)
-}

