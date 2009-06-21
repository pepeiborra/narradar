{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.Processor.UsableRules where

import Control.Applicative
import Data.Monoid

import Narradar.Framework.Proof
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types
import Narradar.Utils

usableRulesP :: (Ppr v, Ppr id, Ord v, Ord a, Enum v, id ~ Identifier a) => Problem id v -> ProblemProofG id v

usableRulesP p@(Problem typ trs dps)
  | (isBNarrowing .|. isGNarrowing) typ = step UsableRulesP p (iUsableRules p pi' (rhs <$> rules dps))
  | otherwise = return p
 where
  pi'  = AF.restrictTo  (getDefinedSymbols dps `mappend` getConstructorSymbols trs ) <$> getAF typ

