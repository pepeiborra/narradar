{-# LANGUAGE ViewPatterns #-}

module Narradar.RewritingProblem where

import Text.XHtml (primHtml, Html)

import Narradar.Proof
import Narradar.Types
import TRS

-- ------------------------
-- Trivial cases
-- ------------------------

trivialP p@(Problem Rewriting{} trs (TRS.rules -> dps))
    | any (\(l:->r) -> show l == show r) dps ||
      all (null.properSubterms.rhs) dps
    = failP Trivial p (primHtml "loop")
    | null dps = success NoPairs p (primHtml "The set of dependency pairs is empty")
    | otherwise = return p
trivialP  p = return p
