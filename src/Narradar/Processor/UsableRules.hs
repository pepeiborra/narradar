{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Narradar.Processor.UsableRules where

import Narradar.Framework
import Narradar.Framework.Ppr

data UsableRulesProof = UsableRulesProof deriving (Eq,Show,Ord)

instance Pretty UsableRulesProof where pPrint _ = text "Usable rules proof"


{-
usableRulesP :: (Pretty v, Pretty id, Ord v, Ord a, Enum v, id ~ Identifier a) => Problem id v -> ProblemProofG id v

usableRulesP p@(Problem typ trs dps)
  | (isBNarrowing .|. isGNarrowing) typ = step UsableRulesP p (iUsableRules p pi' (rhs <$> rules dps))
  | otherwise = return p
 where
  pi'  = AF.restrictTo  (getDefinedSymbols dps `mappend` getConstructorSymbols trs ) <$> getAF typ

-}