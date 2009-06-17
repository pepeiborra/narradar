{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Narradar.ReductionPair where

import Control.Applicative
import Control.Monad
import Control.Monad.Free.Narradar
import Control.Monad.Identity
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import qualified Data.Array.IArray as A
import Data.Foldable (toList)
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import Text.PrettyPrint (Doc,parens, text, int, hcat, punctuate, comma, (<>), (<+>))
import Text.XHtml (Html, toHtml)
import Text.HTML.TagSoup
import System.IO.Unsafe
import Prelude
import qualified Prelude as P

import Lattice
import Narradar.Aprove
import qualified Narradar.ArgumentFiltering as AF
import Narradar.ArgumentFiltering (AF_, PolyHeuristic, MkHeu(..))
import Narradar.ExtraVars
import Narradar.NarrowingProblem
import Narradar.Proof
import Narradar.UsableRules
import Narradar.Utils
import Narradar.Types
import Narradar.TRS
import Narradar.RewritingProblem

aproveXML :: (Ord v, Ppr v, Enum v, Ord id, Ppr id, Lattice (AF_ id)) => Problem id v -> IO String
aproveXML = memoExternalProc (aproveSrvXML OnlyReductionPair 20)

newtype Tuple31 a b c = Tuple31 {tuple31::(a,b,c)}
instance Eq  a => Eq  (Tuple31 a b c) where Tuple31 (a,_,_) == Tuple31 (a',_,_)  =  a == a'
instance Ord a => Ord (Tuple31 a b c) where Tuple31 (a,_,_) `compare` Tuple31 (a',_,_)  =  compare a a'

reductionPair :: (Ord id, Ppr id, Ppr (TermF id Doc), PolyHeuristic heu id (TermF id),
                  MonadFree ProofF m, Lattice (AF_ id), v ~ Var) =>
                 MkHeu heu -> Int -> Problem id v -> [m(Problem id v)]
reductionPair mkH timeout p@(Problem typ@(getAF -> Just pi_g) trs dpsT@(DPTRS dps_a _ unifs _))
    | isAnyNarrowing typ = orProblems where

 (af_constructors, pi_groundInfo) = AF.splitCD p pi_g
 af_init = AF.init p `mappend` af_constructors
 afs = unEmbed $ do
    af0 <- embed (findGroundAF heu pi_groundInfo af_init p R.=<< Set.fromList (rules dpsT))
    let u_p = iUsableRules p (Just af0) (rhs <$> rules dpsT)
    af1 <- embed $ invariantEV heu u_p (AF.restrictTo (getAllSymbols u_p) af0)
    let p' = setTyp  (correspondingRewritingStrategy typ) (iUsableRules u_p (Just af1) (rhs <$> rules dpsT))
        rp = AF.apply af1 $ p'
    return (Tuple31 (rp, af1, p'))   -- forcing unicity of the rewriting problem

 orProblems =
     [ unsafePerformIO $ do
        xml <- aproveXML rp
        return (proofU >>= \p' ->
         let mb_nonDecreasingDPs = findResultingPairs xml
         in case mb_nonDecreasingDPs of
              Nothing -> step (ReductionPair (Just the_af)) p' rp P.>>= \p'' ->
                         failP (External (Aprove "SRV") [OutputXml xml]) p''
              Just basic_nonDecreasingDPs ->
               let text_nonDecreasingDPs = Set.fromList(show <$> (ppr <$$> basic_nonDecreasingDPs))
                   nonDecreasingDPs      = Set.fromList [ i | (i,dp) <- A.assocs dps_a
                                                             , show (pprDP <$> AF.apply the_af dp) `Set.member` text_nonDecreasingDPs]
               in andP (ReductionPair (Just the_af)) p'
                      [ return $ mkProblem typ trs (restrictDPTRS dpsT (toList nonDecreasingDPs))
                      , return $ mkProblem typ trs (restrictDPTRS dpsT [ i | (i,dp) <- A.assocs dps_a
                                                                          , i `Set.notMember` nonDecreasingDPs
                                                                          , not $ isGround $ rhs $ AF.apply pi' dp])])
     | (rp, the_af, up) <- sortBy (flip compare `on` (size . dps . fst3)) (tuple31 <$> Set.toList afs)
     , let proofU = step UsableRulesP p up
     , let pi'   = AF.invert p pi_groundInfo `mappend` the_af
    ]

 heu        = AF.mkHeu mkH p
 pprDP      = foldTerm (\v -> text "v" <> int (fromEnum v)) ppr

reductionPair _ _ p = error ("reductionPair " ++ show(ppr (typ p)))