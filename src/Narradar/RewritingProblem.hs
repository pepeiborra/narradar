{-# LANGUAGE ViewPatterns #-}

module Narradar.RewritingProblem where

import Text.XHtml (primHtml, Html)

import Narradar.Proof
import Narradar.Types


-- ------------------------
-- Trivial cases
-- ------------------------

trivialP p@(Problem Rewriting{} trs (rules -> dps))
    | any (\(l:->r) -> show l == show r) dps ||
      all (null.properSubterms.rhs) dps
    = failP NonTerminationLooping p
    | null dps = success NoPairs p
    | otherwise = return p
trivialP  p = return p
