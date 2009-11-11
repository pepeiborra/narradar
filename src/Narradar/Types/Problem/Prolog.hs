{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Types.Problem.Prolog where

import Control.Applicative
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass
import Text.XHtml (HTML(..), theclass)

import MuTerm.Framework.Problem

import Narradar.Types.Goal
import Narradar.Types.Term (StringId)

import qualified Language.Prolog.Syntax as Prolog

-- -----------------
-- Prolog Problems
-- -----------------

type PrologProblem = Problem (Prolog StringId) (Prolog.Program StringId)

data Prolog id = Prolog {goals_Ptype :: [Goal id]} deriving (Eq,Show,Ord)
instance IsProblem (Prolog id) where
  data Problem (Prolog id) trs = PrologProblem {goals::[Goal id], program :: trs}
  getProblemType = Prolog . goals
  getR = program

instance MkProblem (Prolog id) (Prolog.Program id) where mkProblem (Prolog gg) pgm = PrologProblem gg pgm

prologProblem      = PrologProblem

instance Functor (Problem (Prolog id)) where fmap f (PrologProblem gg a) = PrologProblem gg (f a)


instance Pretty (Prolog id) where pPrint Prolog{..} = text "Prolog"

instance Pretty PrologProblem where
    pPrint PrologProblem{..} =
            text "Prolog problem." $$
            text "Clauses:" <+> pPrint program $$
            text "Goals:" <+> pPrint goals

