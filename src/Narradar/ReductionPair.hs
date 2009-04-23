{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Narradar.ReductionPair where

import Control.Applicative
import Control.Monad
import Control.Monad.Free.Narradar
import Control.Monad.Identity
import Control.RMonad.AsMonad
import qualified Data.Array.IArray as A
import Data.Foldable (toList)
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import Text.PrettyPrint (parens, text, int, hcat, punctuate, comma, (<>), (<+>))
import Text.XHtml (Html, toHtml)
import Text.HTML.TagSoup
import System.IO.Unsafe
import Prelude -- hiding (Monad(..), (=<<))
import qualified Prelude as P

import Lattice
import TRS hiding (Ppr, ppr)
import qualified TRS
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
import Narradar.RewritingProblem

aproveXML :: forall f id. (Ord id, Show id, T id :<: f, DPMark f, TRSC f, Lattice (AF_ id)) => ProblemG id f -> IO String
aproveXML = memoExternalProc (aproveSrvXML OnlyReductionPair 20)

reductionPair :: forall f id heu. (Ord id, Show id, T id :<: f, PolyHeuristic heu id f, DPMark f, TRSC f, Lattice (AF_ id)) => MkHeu heu -> Int -> ProblemG id f -> ProblemProofG id f -- PPT id f Html IO
reductionPair mkH timeout p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps@(DPTRS dps_a _ unifs _)) | isAnyNarrowing typ = msum orProblems where

 afs = unEmbed $ do
    af0 <- embed $ Set.fromList
            (findGroundAF heu pi_groundInfo (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo) p P.=<< rules dps)
    let utrs = tRS(iUsableRules trs (Just af0) (rhs <$> rules dps))
    af1 <- let rr = dps `mappend` utrs in embed $ Set.fromList $ invariantEV heu rr (AF.restrictTo (getAllSymbols rr) af0)
    let utrs' = tRS(iUsableRules utrs (Just af1) (rhs <$> rules dps))
    return (af1, utrs')

 orProblems =
     [ unsafePerformIO $ do
        let rp = AF.apply af $ mkProblem InnermostRewriting trs' dps
        xml <- aproveXML rp
        return (proofU >>= \p' ->
         let mb_nonDecreasingDPs :: Maybe [Rule Basic] = findResultingPairs xml
             the_af = AF.restrictTo (getAllSymbols p') af
         in case mb_nonDecreasingDPs of
              Nothing -> step (ReductionPair (Just the_af)) p' rp P.>>= \p'' ->
                         failP (External (Aprove "SRV") [OutputXml xml]) p''
              Just basic_nonDecreasingDPs ->
               let text_nonDecreasingDPs = Set.fromList(show <$> (ppr <$$> basic_nonDecreasingDPs))
                   nonDecreasingDPs      = Set.fromList [ i | (i,dp) <- A.assocs dps_a
                                                             , show (pprDP <$> AF.apply af dp) `Set.member` text_nonDecreasingDPs]
               in andP (ReductionPair (Just the_af)) p'
                      [ return $ mkProblem typ trs (restrictDPTRS dps (toList nonDecreasingDPs))
                      , return $ mkProblem typ trs (restrictDPTRS dps [ i | (i,dp) <- A.assocs dps_a, i `Set.notMember` nonDecreasingDPs, not $ isGround $ rhs $ AF.apply pi' dp])])
    | (af,trs') <- sortBy (flip compare `on` (dpsSize.fst)) (Set.toList afs)
    , let proofU = step UsableRulesP p (mkProblem typ trs' dps)
    , let pi'    = AF.invert p pi_groundInfo `mappend` af
    ]

 heu        = AF.mkHeu mkH p
 dpsSize af = size (AF.apply af dps)
 pprDP      = foldTerm f where
     f (prj -> Just (Var i n)) = text "v" <> int n
     f t = pprF t

reductionPair _ _ p = error ("reductionPair " ++ show (typ p))