{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Narradar.ReductionPair where

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Control.RMonad.AsMonad
--import "monad-param" Control.Monad.Parameterized
import Data.Foldable (toList)
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import Text.PrettyPrint (parens, text ,hcat, punctuate, comma, (<>), (<+>))
import Text.XHtml (Html, toHtml)
import Text.HTML.TagSoup
import Prelude -- hiding (Monad(..), (=<<))
import qualified Prelude as P

import Lattice
import TRS
import Narradar.Aprove
import qualified Narradar.ArgumentFiltering as AF
import Narradar.ArgumentFiltering (AF_, PolyHeuristic)
import Narradar.ExtraVars
import Narradar.NarrowingProblem
import Narradar.Proof
import Narradar.UsableRules
import Narradar.Utils
import Narradar.Types
import Narradar.TRS

reductionPair :: forall f id heu. (Ord id, Show id, T id :<: f, PolyHeuristic heu id f, DPMark f, TRSC f, Lattice (AF_ id)) => MkHeu heu -> Int -> ProblemG id f -> PPT id f Html IO
reductionPair mkH timeout p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps) | isAnyNarrowing typ = msum orProblems where
 afs = unEmbed $ do
    af0 <- embed $ Set.fromList
            (findGroundAF heu pi_groundInfo (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo) p P.=<< rules dps)
    let utrs = mkTRS(iUsableRules trs (Just af0) (rhs <$> rules dps))
    af1 <- let rr = dps `mappend` utrs in embed $ Set.fromList $ invariantEV heu rr (AF.restrictTo (getAllSymbols rr) af0)
    let utrs' = mkTRS(iUsableRules utrs (Just af1) (rhs <$> rules dps))
    return (af1, utrs')
 orProblems =
    [ wrap' $ do
        let rp = AF.apply af $ mkProblem Rewriting trs' dps
        xml <- aproveSrvXML OnlyReductionPair timeout rp
        return (proofU >>= \p' ->
         let mb_nonDecreasingDPs :: Maybe [Rule Basic] = findResultingPairs (parseTags xml)
             the_af = AF.restrictTo (getAllSymbols p') af
         in case mb_nonDecreasingDPs of
              Nothing -> step (ReductionPair (Just the_af)) p' rp P.>>= \p'' ->
                         failP (External $ Aprove "SRV") p'' (toHtml "NO")
              Just nonDecreasingDPs ->
               let nonDecreasingDPs' = [ dp | dp <- rules dps
                                            , any (\ndp -> show (ppr <$> ndp) == show (pprDP <$> AF.apply af dp)) nonDecreasingDPs]
               in andP (ReductionPair (Just the_af)) p'
                      [ return $ mkProblem typ trs' (mkTRS nonDecreasingDPs')
                      , return $ mkProblem typ trs' (mkTRS [ dp | dp <- rules dps, dp `notElem` nonDecreasingDPs', not $ isGround $ rhs $ AF.apply pi' dp])])
    | (af,trs') <- sortBy (flip compare `on` (dpsSize.fst)) (Set.toList afs)
    , let proofU = step UsableRulesP p (mkProblem typ trs' dps)
    , let pi'    = AF.invert p pi_groundInfo `mappend` af
    ]
 heu        = AF.mkHeu mkH p
 dpsSize af = size (AF.apply af dps)
 pprDP      = foldTerm f where
     f (prj -> Just (Var i n)) = TRS.ppr (var n :: Term Basic)
     f (prj -> Just (T (id::id) [])) = text (show id)
     f (prj -> Just (T (id::id) tt)) =
            text (show id) <> parens (hcat$ punctuate comma tt)
     f t = pprF t
