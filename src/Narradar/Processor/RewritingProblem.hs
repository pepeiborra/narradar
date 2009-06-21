{-# LANGUAGE ViewPatterns #-}

module Narradar.Processor.RewritingProblem where

import Narradar.Framework.Proof
import Narradar.Types


-- ------------------------
-- Trivial cases
-- ------------------------

trivialP p@(Problem Rewriting{} _ (rules -> dps))
    | any (\(l:->r) -> show l == show r) dps ||
      all (null.properSubterms.rhs) dps
    = failP NonTerminationLooping p
    | null dps = success NoPairs p
    | otherwise = return p
trivialP  p = return p
