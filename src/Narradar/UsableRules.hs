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
import TRS

usableRulesP, iUsableRulesP :: forall f id a. (DPMark f, Show id, T id :<: f, id ~ Identifier a) => ProblemG id f -> ProblemProofG id Html f
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

iUsableRulesP p@(Problem typ trs dps@TRS{})
  | (isBNarrowing .|. isGNarrowing) typ = step UsableRulesP p (mkProblem typ trs' dps)
  | otherwise = return p
 where
  pi'  = AF.restrictTo  (getDefinedSymbols dps `mappend` getConstructorSymbols trs ) <$> getGoalAF typ
  trs' = mkTRS(iUsableRules trs pi' (rhs <$> rules dps)) `asTypeOf` trs


-- Assumes Innermost or Constructor Narrowing
-- TODO Extend to work with Q-narrowing to discharge those assumptions
iUsableRules :: (Ord id, TRSC f, TRS trs id f, AF.ApplyAF trs id, DPMark f) => trs -> Maybe (AF.AF_ id) -> [Term f] -> [Rule f]
iUsableRules trs Nothing = F.toList . go mempty where
--  usableRules acc t | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t@(In in_t):rest)
      | isVar t
      = go acc rest
      | rr   <- Set.fromList [r | r <- rules trs
                                , In (icap trs <$> in_t) `unifies` lhs r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])


iUsableRules trs (Just pi) = F.toList . go mempty . map(AF.apply pi) where
  pi_trs = AF.apply pi trs
--  usableRules acc (AF.apply pi -> t) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t@(In in_t):rest)
      | isVar t = go acc rest
      | rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , In (icap pi_trs <$> in_t) `unifies` lhs pi_r]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [AF.apply pi . rhs <$> F.toList new, directSubterms t, rest])

iUsableRules_correct trs (Just pi) = F.toList . go mempty where
  pi_trs = AF.apply pi trs
--  usableRules acc (AF.apply pi -> t) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t:rest)
      | isVar t = go acc rest
      | pi_t@(In in_t) <- AF.apply pi t
      , rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , In (icap pi_trs <$> in_t) `unifies` lhs pi_r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])
