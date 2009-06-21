{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Narradar.Processor.ReductionPair where


import Control.Applicative
import Control.Exception
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import qualified Data.Array.IArray as A
import Data.ByteString.Char8 (pack)
import Data.Foldable (toList)
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import Text.PrettyPrint
import System.IO.Unsafe
import Prelude
import qualified Prelude as P

import Lattice
import Narradar.Constraints.VariableCondition
import Narradar.Framework.Proof
import Narradar.Processor.Aprove
import Narradar.Processor.NarrowingProblem
import Narradar.Utils
import Narradar.Types
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristic, MkHeu(..))

aproveXML :: (Ord v, Ppr v, Enum v, Ord id, Ppr id, Lattice (AF_ id)) => Problem id v -> IO String
aproveXML = memoExternalProc (aproveSrvXML OnlyReductionPair 20)

newtype Tuple31 a b c = Tuple31 {tuple31::(a,b,c)}
instance Eq  a => Eq  (Tuple31 a b c) where Tuple31 (a,_,_) == Tuple31 (a',_,_)  =  a == a'
instance Ord a => Ord (Tuple31 a b c) where Tuple31 (a,_,_) `compare` Tuple31 (a',_,_)  =  compare a a'

reductionPair :: (Ord id, Ppr id, Ppr (TermF id Doc), PolyHeuristic heu id (TermF id),
                  MonadFree ProofF m, Lattice (AF_ id), v ~ Var) =>
                 MkHeu heu -> Int -> Problem id v -> [m(Problem id v)]
reductionPair mkH _timeout p@(Problem typ@(getAF -> Just pi_g) trs dpsT@(DPTRS dps_a _ _ _))
    | isAnyNarrowing typ = orProblems where

 (af_constructors, pi_groundInfo) = AF.splitCD p pi_g
 af_init = AF.init p `mappend` af_constructors
 afs = unEmbed $ do
    let p_f = getVariant p dpsT
    af0    <- embed (findGroundAF heu pi_groundInfo af_init p R.=<< Set.fromList (rules dpsT))
    let u_p = iUsableRules p_f (Just af0) (rhs <$> rules dpsT)
    af1    <- embed $ invariantEV heu u_p (AF.restrictTo (getAllSymbols u_p) af0)
    let p'  = setTyp (correspondingRewritingStrategy typ) (iUsableRules u_p (Just af1) (rhs <$> rules dpsT))
        rp  = AF.apply af1 p'
    return (Tuple31 (rp, af1, p'))   -- forcing unicity of the rewriting problem

 orProblems =
     [ unsafePerformIO $ do
        xml <- aproveXML rp
        return (proofU >>= \p' ->
         let mb_nonDecreasingDPs = findResultingPairs xml
         in case mb_nonDecreasingDPs of
              Nothing -> step (ReductionPair (Just the_af) (pack xml)) p' rp P.>>= \p'' ->
                         failP (External (Aprove "SRV") [OutputXml (pack xml)]) p''
              Just basic_nonDecreasingDPs ->
               let text_nonDecreasingDPs = Set.fromList(show <$> (ppr <$$> basic_nonDecreasingDPs))
                   nonDecreasingDPs      = Set.fromList [ i | (i,dp) <- [0..] `zip` rules (dps up)
                                                             , show (pprDP <$> AF.apply the_af dp) `Set.member` text_nonDecreasingDPs]
               in assert (Set.size nonDecreasingDPs == length basic_nonDecreasingDPs) $
                  andP (ReductionPair (Just the_af) (pack xml)) rp
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
