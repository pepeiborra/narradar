{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types.Problem.NarrowingGen where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Char
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.XHtml (theclass)

import Data.Term
import Data.Term.Rules

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Problem.Infinitary
import Narradar.Framework.Ppr
import Narradar.Utils

import Prelude hiding (pi)

--data GenId id = TheGoal | Gen | NotGen id deriving (Eq, Ord, Show)
--genTerm = term Gen []
--goalTerm = Goal TheGoal

-- -----------------------
-- Terms with Gen and Goal
-- -----------------------

data GenTermF id a = Term id [a]
                   | GenTerm
                   | GoalTerm [a]
   deriving (Eq, Ord, Show)

genTerm  = Impure   GenTerm
goalTerm = Impure . GoalTerm
term id  = Impure . Term id

$(derive makeFunctor     ''GenTermF)
$(derive makeFoldable    ''GenTermF)
$(derive makeTraversable ''GenTermF)

data GenId id = AnId id | GenId | GoalId deriving (Eq, Ord, Show)

instance Pretty id => Pretty (GenId id) where
  pPrint GenId  = text "GEN"
  pPrint GoalId = text "GOAL"
  pPrint (AnId id) = pPrint id

instance Ord id => HasId (GenTermF id) where
  type TermId (GenTermF id) = GenId id
  getId (Term id  _) = Just (AnId id)
  getId (GenTerm   ) = Just GenId
  getId (GoalTerm _) = Just GoalId

instance MapId GenTermF where
  mapId f (Term id  tt) = Term (f id) tt
  mapId _ (GenTerm    ) = GenTerm
  mapId _ (GoalTerm tt) = GoalTerm tt


instance (Pretty a, Pretty id) => Pretty (GenTermF id a) where
    pPrint (Term n []) = pPrint n
    pPrint (Term n [x,y]) | not (any isAlpha $ show $ pPrint n) = pPrint x <+> pPrint n <+> pPrint y
    pPrint (Term n tt) = pPrint n <> parens (hcat$ punctuate comma$ map pPrint tt)
    pPrint (GoalTerm tt) = text "GOAL" <> parens (hcat $ punctuate comma $ map pPrint tt)
    pPrint GenTerm     = text "GEN"


-- --------------------------------------------------------------
-- The class of Narrowing-as-Rewriting-with-Generators problems
-- --------------------------------------------------------------
type NarrowingGen  = MkNarrowingGen Rewriting
type CNarrowingGen = MkNarrowingGen IRewriting
instance GetPairs NarrowingGen where getPairs _ = getNPairs

data MkNarrowingGen p = NarrowingGen {baseProblemType :: p} deriving (Eq, Ord, Show)

instance (IsDPProblem p, Functor (DPProblem p)) => IsDPProblem (MkNarrowingGen p) where
  data DPProblem (MkNarrowingGen p) a    = NarrowingGenProblem {baseProblem::DPProblem p a}
  getProblemType (NarrowingGenProblem p) = NarrowingGen (getProblemType p)
  getP   (NarrowingGenProblem p) = getP p
  getR   (NarrowingGenProblem p) = getR p
  mapR f (NarrowingGenProblem p) = NarrowingGenProblem (mapR f p)
  mapP f (NarrowingGenProblem p) = NarrowingGenProblem (mapP f p)
instance MkDPProblem p trs => MkDPProblem (MkNarrowingGen p) trs where
  mkDPProblem (NarrowingGen typ) = (narrowingGenProblem.) . mkDPProblem typ

narrowingGen        = NarrowingGen  Rewriting
cnarrowingGen       = NarrowingGen  IRewriting
narrowingGenProblem = NarrowingGenProblem

-- ----------
-- Instances
-- ----------

deriving instance (Eq (DPProblem p trs)) => Eq (DPProblem (MkNarrowingGen p) trs)
deriving instance (Ord (DPProblem p trs)) => Ord (DPProblem (MkNarrowingGen p) trs)
deriving instance (Show (DPProblem p trs)) => Show (DPProblem (MkNarrowingGen p) trs)

-- Functor

instance Functor (DPProblem p) => Functor (DPProblem (MkNarrowingGen p)) where fmap f (NarrowingGenProblem p) = NarrowingGenProblem (fmap f p)
instance Foldable (DPProblem p) => Foldable (DPProblem (MkNarrowingGen p)) where foldMap f (NarrowingGenProblem p) = foldMap f p
instance Traversable (DPProblem p) => Traversable (DPProblem (MkNarrowingGen p)) where traverse f (NarrowingGenProblem p) = NarrowingGenProblem <$> traverse f p

$(derive makeFunctor     ''MkNarrowingGen)
$(derive makeFoldable    ''MkNarrowingGen)
$(derive makeTraversable ''MkNarrowingGen)

-- Output

instance Pretty p => Pretty (MkNarrowingGen p) where
    pPrint NarrowingGen{..} = text "NarrowingGen" <+> pPrint baseProblemType

instance HTMLClass (MkNarrowingGen Rewriting) where htmlClass _ = theclass "IRew"
instance HTMLClass (MkNarrowingGen IRewriting) where htmlClass _ = theclass "INarr"

instance ApplyAF (Term (GenTermF id) v) where
   type AFId (Term (GenTermF id) v) = GenId id
   apply af = foldTerm return f
     where
       f t@(Term n tt)
         | Just ii <- AF.lookup' (AnId n) af = either (\i  -> term n [tt !! pred i])
                                               (\ii -> term n (select tt (pred <$> ii)))
                                               ii
         | otherwise = Impure t

       f (GoalTerm tt)
         | Just ii <- AF.lookup' GoalId af = either (\i  -> goalTerm [tt !! i])
                                                    (\ii -> goalTerm (select tt (pred <$> ii)))
                                                    ii
       f GenTerm = genTerm

-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (MkNarrowingGen p, trs)
  where
    icap (NarrowingGen{..},trs) = icap (baseProblemType,trs)

-- Usable Rules

instance (Enum v, Unify t, Ord (Term t v), IsTRS t v trs, GetVars v trs
         ,ApplyAF (Term t v), ApplyAF trs
         , id ~ AFId trs, AFId (Term t v) ~ id, Ord id
         ,IUsableRules t v (p,trs), ICap t v (p,trs)) =>
   IUsableRules t v (MkNarrowingGen p, trs)
 where
   iUsableRulesM (typ@NarrowingGen{..}, trs) tt = do
      (_,trs') <- iUsableRulesM (baseProblemType,trs) tt
      return (typ, trs')

   iUsableRulesVar (NarrowingGen{..},trs) = iUsableRulesVar (baseProblemType, trs)