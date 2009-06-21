{-# LANGUAGE PatternGuards, ViewPatterns #-}
module Narradar.Processor.ExtraVars where

import Control.Monad
import qualified Data.Set as Set

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (mkHeu)
import qualified  Narradar.Types.ArgumentFiltering as AF
import Narradar.Types
import Narradar.Framework.Proof


evProcessor _ p | not (isAnyNarrowingProblem p) = return p
evProcessor mkH p@Problem{typ=(getAF -> Just af)}
     | null extra      = return p
     | null orProblems = failP EVProcFail p
     | otherwise       = msum (map return orProblems)
  where extra      = extraVars p
        heu        = mkHeu mkH p
        orProblems = [(p `withAF` af') | af' <- Set.toList $ invariantEV heu p af]

evProcessor mkH p = evProcessor mkH (p `withAF` AF.init p)
evProcessor _ p = return p
