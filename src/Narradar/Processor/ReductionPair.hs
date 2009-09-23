{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances #-}

module Narradar.Processor.ReductionPair where


import Control.Applicative
import Control.Exception
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import qualified Data.Array.IArray as A
import Data.ByteString.Char8 (pack, unpack)
import Data.Foldable (toList)
import Data.Traversable (Traversable)
import Data.List
import Data.Monoid
import qualified Data.Set as Set
import System.IO.Unsafe
import Prelude
import qualified Prelude as P

import Lattice
import Narradar.Constraints.VariableCondition
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Processor.Aprove
import Narradar.Processor.NarrowingProblem (findGroundAF')
import Narradar.Processor.UsableRules
import Narradar.Types
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristic, MkHeu(..))
import Narradar.Utils
import Narradar.Utils.Html

data AProveReductionPairProcessor heu = AProveReductionPairProcessor (MkHeu heu) Int

instance (p0  ~ DPProblem typ trs, PprTPDB p0, Ord p0, ProofInfo p0
         ,trs ~ NTRS id Var
         ,t   ~ TermF id, Pretty (t Doc)
         ,IsDPProblem typ, Pretty typ, Traversable(DPProblem typ)
         ,ICap t Var (typ, trs), IUsableRules t Var (typ, trs)
         ,Pretty id, Ord id, Lattice (AF_ id), PolyHeuristic heu id
         ,HTMLClass (MkNarrowingGoal id typ)) =>
    Processor (AProveReductionPairProcessor heu)
              (DPProblem (MkNarrowingGoal id typ) (NTRS id Var))
              (DPProblem (MkNarrowingGoal id typ) (NTRS id Var))
 where
  applySearch (AProveReductionPairProcessor mkH timeout) p
    = orProblems
   where
    NarrowingGoal pi_g basetyp = getProblemType p
    dps = getP p
    (af_constructors, pi_groundInfo) = AF.splitCD p pi_g
    af_init = AF.init p `mappend` af_constructors
    afs = unEmbed $ do
       let p_f = getVariant p dps
       af0    <- embed (findGroundAF' heu pi_groundInfo af_init p R.=<< Set.fromList (rules dps))
       let u_p = iUsableRules (mkNewProblem (NarrowingGoal af0 basetyp) p_f) (rhs <$> rules dps)
       af1    <- embed $ invariantEV heu u_p (AF.restrictTo (getAllSymbols u_p) af0)
       let u_p' = iUsableRules (mkNewProblem (NarrowingGoal af1 basetyp) u_p) (rhs <$> rules dps)
           rp   = AF.apply af1 (mkNewProblem basetyp u_p')
       return (Tuple31 (rp, af1, u_p'))   -- forcing unicity of the rewriting problem

    orProblems =
     [ unsafePerformIO $ do
        xml <- aproveXML timeout rp
        return (proofU >>= \p' ->
         let mb_nonDecreasingDPs = findResultingPairs xml
         in case mb_nonDecreasingDPs of
              Nothing -> singleP (AProveReductionPairProof the_af [OutputXml $ pack xml]) p' rp P.>>= \p'' ->
                         failP AProveReductionPairFail p''
              Just basic_nonDecreasingDPs ->
               let text_nonDecreasingDPs = Set.fromList(show <$> (pPrint <$$> basic_nonDecreasingDPs))
                   nonDecreasingDPs      = Set.fromList [ i | (i,dp) <- [0..] `zip` rules (getP up)
                                                             , show (pprDP <$> AF.apply the_af dp) `Set.member` text_nonDecreasingDPs]
               in assert (Set.size nonDecreasingDPs == length basic_nonDecreasingDPs) $
                  andP (AProveReductionPairProof the_af [OutputXml $ pack xml]) rp
                      [ setP (restrictDPTRS dps (toList nonDecreasingDPs)) p
                      , setP (restrictDPTRS dps [ i | (i,dp) <- zip [0..] (rules dps)
                                                    , i `Set.notMember` nonDecreasingDPs
                                                    , not $ isGround $ rhs $ AF.apply pi' dp])
                                      p])
     | (rp, the_af, up) <- sortBy (flip compare `on` (size . getP . fst3)) (tuple31 <$> Set.toList afs)
     , let proofU = singleP UsableRulesProof p up
     , let pi'   = AF.invert p pi_groundInfo `mappend` the_af
     ]

    heu   = AF.mkHeu mkH p
    pprDP = foldTerm (\v -> text "v" <> int (fromEnum v)) pPrint

-- -------
-- Proof
-- -------

data AProveReductionPairProof id where AProveReductionPairProof :: AF_ id -> [Output] -> AProveReductionPairProof id
                                       AProveReductionPairFail :: AProveReductionPairProof ()


instance Pretty (AProveReductionPairProof id) where pPrint _ = text "External: Aprove (Reduction Pair)"

instance HTML (AProveReductionPairProof id) where
 toHtml (AProveReductionPairProof _ outputs)
     | Just (OutputHtml html) <- find isOutputHtml outputs = thickbox (unpack html) << spani "seeproof" << "(see proof)"

instance ProofInfo (AProveReductionPairProof id)

-- ----------------
-- Implementation
-- ----------------

--aproveXML :: (Ord v, Pretty v, Enum v, Ord id, Pretty id, Lattice (AF_ id)) => Int -> DPProblem typ trs -> IO String
aproveXML timeout = memoExternalProc (aproveSrvXML OnlyReductionPair timeout)

newtype Tuple31 a b c = Tuple31 {tuple31::(a,b,c)}
instance Eq  a => Eq  (Tuple31 a b c) where Tuple31 (a,_,_) == Tuple31 (a',_,_)  =  a == a'
instance Ord a => Ord (Tuple31 a b c) where Tuple31 (a,_,_) `compare` Tuple31 (a',_,_)  =  compare a a'

