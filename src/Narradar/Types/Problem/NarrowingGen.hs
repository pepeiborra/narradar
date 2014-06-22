{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DisambiguateRecordFields, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable, DeriveGeneric #-}

module Narradar.Types.Problem.NarrowingGen where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad.Free
import           Data.Data
import           Data.Foldable                    (Foldable(..))
import           Data.Hashable
import           Data.Traversable                 as T (Traversable(..))
import qualified Data.Set                         as Set
import           Data.Typeable
import           Text.XHtml                       (theclass)

import           Data.Term                        hiding (TermF)
import qualified Data.Term.Family                 as Family
import           Data.Term.Rules

import           MuTerm.Framework.Problem

import           Narradar.Types.DPIdentifiers
import           Narradar.Types.Problem
import           Narradar.Types.Problem.Rewriting
import           Narradar.Types.Term
import           Narradar.Types.TRS
import           Narradar.Framework
import           Narradar.Framework.Ppr

import           Prelude                          hiding (pi)

import GHC.Generics (Generic)
import Debug.Hoed.Observe

-- -----------------------
-- Terms with Gen and Goal
-- -----------------------

data GenId id = AnId id | GenId | GoalId deriving (Eq, Ord, Show, Typeable, Generic)

instance Pretty id => Pretty (GenId id) where
  pPrint GenId  = text "GEN"
  pPrint GoalId = text "GOAL"
  pPrint (AnId id) = pPrint id

instance Pretty (GenId String) where
  pPrint GenId  = text "GEN"
  pPrint GoalId = text "GOAL"
  pPrint (AnId id) = text id

instance Hashable a => Hashable (GenId a) where
  hashWithSalt s GenId  = hashWithSalt s (1::Int)
  hashWithSalt s GoalId = hashWithSalt s (2::Int)
  hashWithSalt s (AnId id) = hashWithSalt (3::Int) (hashWithSalt s id)

instance NFData a => NFData (GenId a) where
  rnf GenId = ()
  rnf GoalId = ()
  rnf (AnId id) = rnf id


class GenSymbol id where
  isGenSymbol  :: id -> Bool
  isGoalSymbol :: id -> Bool
  goalSymbol   :: id
  genSymbol    :: id

instance GenSymbol (GenId id) where
   genSymbol = GenId; goalSymbol = GoalId
   isGenSymbol  GenId  = True; isGenSymbol  _ = False
   isGoalSymbol GoalId = True; isGoalSymbol _ = False

instance GenSymbol a => GenSymbol (DPIdentifier a) where
  genSymbol = IdFunction genSymbol; goalSymbol = IdFunction goalSymbol
  isGenSymbol (IdFunction id) = isGenSymbol id
  isGenSymbol (IdDP id) = isGenSymbol id
  isGoalSymbol (IdFunction id) = isGoalSymbol id
  isGoalSymbol (IdDP id) = isGoalSymbol id
--instance GenSymbol StringId where genSymbol = StringId "gen" 0; goalSymbol

-- --------------------------------------------------------------
-- The class of Narrowing-as-Rewriting-with-Generators problems
-- --------------------------------------------------------------
type NarrowingGen  = MkNarrowingGen Rewriting
type CNarrowingGen = MkNarrowingGen IRewriting
type INarrowingGen = MkNarrowingGen IRewriting
--instance GetPairs NarrowingGen where getPairs _ = getNPairs

data MkNarrowingGen p = NarrowingGen {baseFramework :: p}
          deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable, Generic)

instance FrameworkExtension MkNarrowingGen where
  getBaseFramework = baseFramework
  getBaseProblem (NarrowingGenProblem p) = p
  liftProblem   f p = f (baseProblem p) >>= \p0' -> return p{baseProblem = p0'}
  liftFramework f (NarrowingGen b) = NarrowingGen (f b)
  liftProcessorS = liftProcessorSdefault


instance IsProblem p => IsProblem (MkNarrowingGen p) where
  newtype Problem (MkNarrowingGen p) a      = NarrowingGenProblem {baseProblem::Problem p a}
  getFramework (NarrowingGenProblem p) = NarrowingGen (getFramework p)
  getR   (NarrowingGenProblem p)         = getR p

instance MkProblem p trs => MkProblem (MkNarrowingGen p) trs where
  mkProblem (NarrowingGen p) rr = NarrowingGenProblem (mkProblem p rr)
  mapR f (NarrowingGenProblem p) = NarrowingGenProblem (mapR f p)

instance IsDPProblem p => IsDPProblem (MkNarrowingGen p) where
  getP   (NarrowingGenProblem p) = getP p


instance (Ord id, GenSymbol id, MkDPProblem p (NTRS id)) =>
  MkDPProblem (MkNarrowingGen p) (NTRS id)
 where
  mapP f (NarrowingGenProblem p) = NarrowingGenProblem (mapP f p)
  mkDPProblem (NarrowingGen typ) trs dps
         = NarrowingGenProblem $ mkDPProblem typ trs' dps'
   where
    trs' = mapNarradarTRS' id extraVarsToGen trs
    dps' = mapNarradarTRS' id extraVarsToGen dps

narrowingGen  = NarrowingGen  rewriting
cnarrowingGen = NarrowingGen  irewriting

-- ----------
-- Instances
-- ----------

deriving instance (Eq (Problem p trs)) => Eq (Problem (MkNarrowingGen p) trs)
deriving instance (Ord (Problem p trs)) => Ord (Problem (MkNarrowingGen p) trs)
deriving instance (Show (Problem p trs)) => Show (Problem (MkNarrowingGen p) trs)

-- Functor

instance Functor (Problem p) => Functor (Problem (MkNarrowingGen p)) where fmap f (NarrowingGenProblem p) = NarrowingGenProblem (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (MkNarrowingGen p)) where foldMap f (NarrowingGenProblem p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (MkNarrowingGen p)) where traverse f (NarrowingGenProblem p) = NarrowingGenProblem <$> traverse f p

-- Data.Term instances

-- NFData

instance NFData (Problem p trs) => NFData (Problem (MkNarrowingGen p) trs) where
  rnf (NarrowingGenProblem p) = rnf p

-- Output

instance Pretty p => Pretty (MkNarrowingGen p) where
    pPrint NarrowingGen{..} = text "NarrowingGen" <+> pPrint baseFramework

instance HTMLClass (MkNarrowingGen Rewriting) where htmlClass _ = theclass "GenNarr"
instance HTMLClass (MkNarrowingGen IRewriting) where htmlClass _ = theclass "GenCNarr"

instance (t ~ Family.TermF trs
         ,HasRules trs, GetVars trs
         ,HasId t, Pretty (Family.Id t), Foldable t
         ,IsDPProblem base, PprTPDB (Problem base trs)
         ) => PprTPDB (Problem (MkNarrowingGen base) trs) where
  pprTPDB p@NarrowingGenProblem{..} = pprTPDB baseProblem


-- ICap
instance ICap (st, NarradarTRS t v) => ICap (MkNarrowingGen st, NarradarTRS t v) where
  icapO = liftIcapO

-- Usable Rules

instance (IUsableRules base trs) => IUsableRules (MkNarrowingGen base) trs where
   iUsableRulesM    = liftUsableRulesM
   iUsableRulesVarM = liftUsableRulesVarM

-- Insert Pairs

instance (MkDPProblem (MkNarrowingGen base) trs, InsertDPairs base trs) => InsertDPairs (MkNarrowingGen base) trs where
  insertDPairs NarrowingGenProblem{..} = NarrowingGenProblem . insertDPairs baseProblem

-- Hood
instance Observable a => Observable (MkNarrowingGen a)
instance Observable a => Observable (GenId a)
-- -------------------
-- Support functions
-- -------------------

extraVarsToGen :: (Ord v, GenSymbol id) => Rule (TermF id) v -> Rule (TermF id) v
extraVarsToGen (l :-> r) = l :-> applySubst sigma r
     where
      sigma = fromListSubst (evars `zip` repeat genTerm)
      genTerm = term genSymbol []
      evars = Set.toList(getVars r `Set.difference` getVars l)
