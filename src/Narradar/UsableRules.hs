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

usableRulesP, iUsableRulesP :: forall f id a. (DPMark f, Show id, T id :<: f, Ord a, id ~ Identifier a) => ProblemG id f -> ProblemProofG id Html f
usableRulesP p@(Problem typ trs dps@TRS{}) | (isBNarrowing .|. isGNarrowing) typ
   = step UsableRulesNaiveP p (mkProblem typ trs' dps)
 where
  dps' = maybe (rules dps) (`AF.apply` rules dps) (getGoalAF typ)
  trs' = mkTRS (concat (usableRules mempty <$> rhs <$> dps'))
  usableRules seen t = let ff  = Set.fromList [f | u <- subterms t, Just f <- [rootSymbol u]]
                                 `Set.intersection` getDefinedSymbols trs
                           new = Set.difference ff seen
                           rr  = [r | r <- rules trs, fromJust(rootSymbol(lhs r)) `Set.member` new]
                       in rr ++ concat (usableRules (ff `mappend` seen) <$> rhs <$> rr)

usableRulesP p = return p

iUsableRulesP p@(Problem typ trs dps)
  | (isBNarrowing .|. isGNarrowing) typ = step UsableRulesP p (mkProblem typ trs' dps)
  | otherwise = return p
 where
  pi'  = AF.restrictTo  (getDefinedSymbols dps `mappend` getConstructorSymbols trs ) <$> getGoalAF typ
  trs' = mkTRS(iUsableRules trs pi' (rhs <$> rules dps)) `asTypeOf` trs

