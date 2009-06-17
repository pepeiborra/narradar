{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.UsableRules where

import Control.Applicative
import qualified Data.Foldable as F
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Text.XHtml (Html)

import Narradar.DPIdentifiers
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Proof
import Narradar.Types
import Narradar.Utils

usableRulesP :: (Ppr v, Ppr id, Ord v, Ord a, Enum v, id ~ Identifier a) => Problem id v -> ProblemProofG id v

usableRulesP p@(Problem typ trs dps)
  | (isBNarrowing .|. isGNarrowing) typ = step UsableRulesP p (mkProblem typ trs' dps)
  | otherwise = return p
 where
  pi'  = AF.restrictTo  (getDefinedSymbols dps `mappend` getConstructorSymbols trs ) <$> getAF typ
  trs' = tRS(iUsableRules trs pi' (rhs <$> rules dps)) `asTypeOf` trs

