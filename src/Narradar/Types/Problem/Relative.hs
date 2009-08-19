{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
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

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr

data Relative trs p = Relative {relativeTRS_PType::trs, baseProblemType::p} deriving (Eq, Ord, Show)
instance IsDPProblem p => IsDPProblem (Relative trs0 p) where
  data DPProblem (Relative trs0 p) trs = RelativeProblem {relativeTRS::trs0, baseProblem::DPProblem p trs}
  getProblemType (RelativeProblem r0 p) = Relative r0 (getProblemType p)
  mkDPProblem (Relative trs0 p) = (RelativeProblem trs0 .) . mkDPProblem p
  getR (RelativeProblem _ p) = getR p
  getP (RelativeProblem _ p) = getP p
  mapR f (RelativeProblem r0 p) = RelativeProblem r0 (mapR f p)
  mapP f (RelativeProblem r0 p) = RelativeProblem r0 (mapP f p)

relativeProblem          = RelativeProblem

deriving instance (Eq trs, Eq (DPProblem p trs)) => Eq (DPProblem (Relative trs p) trs)
deriving instance (Ord trs, Ord (DPProblem p trs)) => Ord (DPProblem (Relative trs p) trs)
deriving instance (Show trs, Show (DPProblem p trs)) => Show (DPProblem (Relative trs p) trs)

instance Functor (DPProblem p) => Functor (DPProblem (Relative trs0 p)) where fmap f (RelativeProblem r0 p) = RelativeProblem r0 (fmap f p)
instance Foldable (DPProblem p) => Foldable (DPProblem (Relative trs0 p)) where foldMap f (RelativeProblem r0 p) = foldMap f p
instance Traversable (DPProblem p) => Traversable (DPProblem (Relative trs0 p)) where traverse f (RelativeProblem r0 p) = RelativeProblem r0 <$> traverse f p


$(derive makeFunctor     ''Relative)
$(derive makeFoldable    ''Relative)
$(derive makeTraversable ''Relative)


instance (IsDPProblem p, Ord (SignatureId trs), HasSignature (DPProblem p trs), Monoid trs) =>
    HasSignature (DPProblem (Relative trs p) trs)
  where
--    type SignatureId (DPProblem (Relative trs p) trs) = SignatureId trs
    getSignature (RelativeProblem r0 p) = getSignature (mapR (`mappend` r0) p)


-- Output

instance Ppr p => Ppr (Relative trs p)
    where
         ppr (Relative _ p) = text "Relative termination of" <+> ppr p

-- Construction

instance (Ord id, HasRules (TermF id) Var trs0, MkNarradarProblem p id) =>
    MkNarradarProblem (Relative trs0 p) id
 where
  type Typ' (Relative trs0 p) id = Relative (NarradarTRS (Identifier id) Var) (Typ' p id)
  mkNarradarProblem (Relative trs0 typ) trs = relativeProblem trs0' p where
      p     = mkNarradarProblem typ trs
      trs0' = tRS $ mapTermSymbols IdFunction <$$> rules trs0


-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
         ICap t v (Relative trs p, trs)
 where
         icap (Relative _ p,trs) = icap (p,trs)

-- Usable Rules

instance (Ord v, Ord (Term t v), IsTRS t v trs, Monoid trs, IsDPProblem typ, IUsableRules t v (typ, trs)) =>
   IUsableRules t v (DPProblem (Relative trs typ) trs)
    where
      iUsableRulesM (RelativeProblem r0 p) tt = do
            let rr  = getR p
            (_, usableRulesTRS) <- iUsableRulesM (getProblemType p, r0 `mappend` rr) tt
            let usableRulesSet = Set.fromList (rules usableRulesTRS :: [Rule t v])
                rr' = tRS $ toList (Set.fromList (rules rr) `Set.intersection` usableRulesSet)
                r0' = tRS $ toList (Set.fromList (rules r0) `Set.intersection` usableRulesSet)
            return (RelativeProblem r0' (setR rr' p))
      iUsableRulesVar (RelativeProblem r0 p) = iUsableRulesVar (getProblemType p, r0 `mappend` getR p)
