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

import Narradar.DPairs
import Narradar.DPIdentifiers
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Proof
import Narradar.Types
import TRS

usableProcessor, iUsableProcessor :: forall f id a. (DPMark f, Show id, T id :<: f, id ~ Identifier a) => ProblemG id f -> ProblemProofG id Html f
usableProcessor p@(Problem typ trs dps@TRS{}) | isBNarrowing typ
   = step UsableRulesP p (mkProblem typ trs' dps)
 where
  dps' = maybe (rules dps) (`AF.apply` rules dps) (getGoalAF typ)
  trs' = mkTRS (concat (usableRules mempty <$> rhs <$> dps'))
  usableRules seen t = let ff  = Set.fromList [f | u <- subterms t, Just f <- [rootSymbol u]]
                                 `Set.intersection` getDefinedSymbols trs
                           new = Set.difference ff seen
                           rr  = [r | r <- rules trs, fromJust(rootSymbol(lhs r)) `Set.member` new]
                       in rr ++ concat (usableRules (ff `mappend` seen) <$> rhs <$> rr)

usableProcessor p = return p

-- FIX Is this a sound approximation of the Usable Rules ?
--     I don't think so, as here we use pi to filter the rules too, but
--     later we will use a more flexible version that filters less in the rules,
--     but the same in the pairs.
--     Fix it by using a version of pi restricted to DP symbols here.
iUsableProcessor p@(Problem typ@(getGoalAF -> Just pi) trs dps@TRS{}) | isBNarrowing typ
   = step UsableRulesP p (mkProblem typ trs' dps)
 where
  pi'  = AF.filter ((isDPSymbol.) . const) pi
  trs' = mkTRS (F.toList $ usableRules mempty (rhs <$> pi_dps))
  pi_dps = AF.apply pi (rules dps)
  pi_trs = mkTRS(AF.apply pi (rules trs)) :: NarradarTRS id f
  usableRules acc [] = acc
  usableRules acc (t@(In in_t):rest)
      | isVar t
      = usableRules acc rest
      | rr   <- Set.fromList [r | r <- rules trs, let r' = AF.apply pi r, In (icap pi_trs <$> in_t) `unifies` lhs r' ]
      , new  <- Set.difference rr acc
      = usableRules (rr `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])

iUsableProcessor p = return p
