{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Types.Problem.Prolog where

import Data.Monoid
import Data.Term
import Data.Term.Rules
import qualified Language.Prolog.Syntax as Prolog

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Utils
import Narradar.Framework.Ppr


data PrologProblem = PrologProblem {goals::[AF_ String], program::Prolog.Program String}
prologProblem      = PrologProblem


instance HasSignature (PrologProblem) where
  type SignatureId PrologProblem = String
  getSignature (PrologProblem _ clauses) = getSignature clauses

instance Ppr PrologProblem where
    ppr PrologProblem{..} =
            text "Prolog problem." $$
            text "Clauses:" <+> ppr program $$
            text "Goals:" <+> ppr goals
