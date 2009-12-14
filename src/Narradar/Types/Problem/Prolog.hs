{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Types.Problem.Prolog where

import Control.Applicative hiding (many)
import Control.Monad.Error
import Data.Bifunctor
import Data.ByteString.Char8 (ByteString, pack)
import Data.Foldable as F (Foldable(..), toList)
import Data.Maybe (catMaybes)
import Data.Term
import Data.Traversable (Traversable)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJClass
import Text.XHtml (HTML(..), theclass)
import Prelude as P

import qualified Language.Prolog.Parser as Prolog hiding (term)

import MuTerm.Framework.Problem
import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Term (StringId)
import Narradar.Utils

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


-- --------------------------
-- Parsing Prolog problems
-- --------------------------

instance Error ParseError

prologParser = do
  txt    <- getInput
  goals  <- eitherM $ mapM parseGoal $ catMaybes $ map f (lines txt)
  clauses<- Prolog.whiteSpace *> many Prolog.clause <* eof
  return (prologProblem (upgradeGoal <$> concat goals) (upgradeIds (concat clauses)))
  where
    f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
    f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
    f _ = Nothing

    upgradeIds :: Prolog.Program String -> Prolog.Program (ArityId ByteString)
    upgradeIds = fmap2 (upgradePred . fmap (foldTerm return upgradeTerm))

    upgradeGoal (Goal id mm) = Goal (ArityId (pack id) (length mm)) mm

    upgradeTerm (Prolog.Term id tt) = Prolog.term (ArityId (pack id) (length tt)) tt
    upgradeTerm t                   = Impure $ bimap ((`ArityId` 0) . pack) P.id t
    upgradePred (Prolog.Pred id tt) = Prolog.Pred (ArityId (pack id) (length tt)) tt
    upgradePred p                   = bimap ((`ArityId` 0) . pack) P.id p

