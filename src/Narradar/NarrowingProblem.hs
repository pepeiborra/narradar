{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns, RecordPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}


module Narradar.NarrowingProblem (
     mkGoalProblem, -- mkGoalProblem_rhs,
     groundRhsOneP, groundRhsAllP, uGroundRhsAllP, uGroundRhsOneP,
     safeAFP,
     MkHeu(..)) where

import Control.Applicative
import Control.Exception
import Control.Monad hiding (join, mapM)
import Control.Monad.Free hiding (note)
import Control.Monad.Writer(execWriter, execWriterT, MonadWriter(..), lift)
import Control.Monad.State (evalState, evalStateT, modify, MonadState(..))
import Control.RMonad.AsMonad
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (intersect, (\\), sortBy)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)
import Data.Traversable
import Text.XHtml (toHtml, Html)
import Prelude hiding (mapM, pi)

import Narradar.ArgumentFiltering (AF_,AF, LabelledAF, Heuristic(..), bestHeu, typeHeu, MkHeu, mkHeu)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPairs
import Narradar.Proof
import Narradar.Utils
import Narradar.Types as Narradar
import Narradar.ExtraVars
import Narradar.UsableRules
import Narradar.Aprove
import TRS
import Lattice
import Language.Prolog.TypeChecker

#ifdef DEBUG
import Debug.Observe
#endif


mkGoalProblem mkHeu typ@GNarrowingModes{} trs = mkGoalProblem' typ GNarrowing mkHeu trs
mkGoalProblem mkHeu typ@BNarrowingModes{} trs = mkGoalProblem' typ BNarrowing mkHeu trs
mkGoalProblem _     typ                   trs = [mkDPProblem typ trs]

--mkGoalProblem' :: ProblemType id -> ProblemType id ->
mkGoalProblem' typGoal typ heu trs | const True (typGoal `asTypeOf` typ) =
    let p@(Problem _ trs' dps) = mkDPProblem typ trs
        extendedPi = AF.extendAFToTupleSymbols (pi typGoal)
        goal'      = AF.mapSymbols functionSymbol (goal typGoal)
        orProblems = case (mkHeu heu p) of
                       heu | isSafeOnDPs heu -> [Problem typGoal{pi=extendedPi,goal=goal'} trs' dps]
                       heu -> [assert (isSoundAF pi' p) $
                               Problem typGoal{pi=pi', goal=goal'} trs' dps
                                   | pi' <- invariantEV heu (rules p) extendedPi]
    in assert (not $ null orProblems) orProblems

-- ------------------------------------------------------------------------
-- This is the AF processor described in our Dependency Pairs for Narrowing
-- ------------------------------------------------------------------------
{-# off SPECIALIZE groundRhsOneP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# off SPECIALIZE groundRhsOneP :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
-- groundRhsOneP :: (Lattice (AF_ id), Show id, Ord id, T id :<: f, DPMark f) => ProblemG id f -> ProblemProofG id Html f
groundRhsOneP mk p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps)
  | isAnyNarrowingProblem p =
    if null orProblems
      then failP (GroundOne Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where heu        = mkHeu mk p -- maybe (bestHeu p) typeHeu (getTyping typ)
          afs        = findGroundAF heu pi_groundInfo (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo) p =<< rules dps
          orProblems = [ step (GroundOne (Just af)) p $
                                AF.apply af (mkProblem Rewriting trs dps)
                        | af <- afs]

groundRhsOneP mkHeu p@(Problem (getGoalAF -> Nothing) trs dps)
  | isAnyNarrowingProblem p = groundRhsOneP mkHeu (p `withGoalAF` AF.init p)
  | otherwise = return p

findGroundAF heu pi_groundInfo af0 p (_:->r)
  | isVar r   = mzero
  | otherwise = (toList(mkGround r) >>= invariantEV heu p)
            where
          --    assertGroundDP af = let af' = goalAF_inv `mappend` af in assert (isGround $ AF.apply af' r) af
              mkGround t = cutWith heu af0 t varsp -- TODO Fix: cut one at a time
                  where varsp = [TRS.note v | v <- vars' (annotateWithPos t)] \\\
                                [TRS.note v | v <- subterms (AF.apply pi_groundInfo $ annotateWithPos t)]

-- ------------------------------------------------------------------------
-- A variation for use with SCCs
-- ------------------------------------------------------------------------
{-# off SPECIALIZE groundRhsAllP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# off SPECIALIZE groundRhsAllP :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
-- groundRhsAllP :: (Lattice (AF_ id), Show id, T id :<: f, Ord id, DPMark f) => ProblemG id f -> ProblemProofG id Html f
groundRhsAllP mk p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then failP (GroundAll Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where heu        = mkHeu mk p -- maybe (bestHeu p) typeHeu (getTyping typ)
          afs        = foldM (\af -> findGroundAF heu pi_groundInfo af p)
                             (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo)
                             (rules dps)
          orProblems = [ step (GroundAll (Just af)) p $
                                AF.apply af (mkProblem Rewriting trs dps)
                        | af <- afs]

groundRhsAllP mkHeu p@(Problem (getGoalAF -> Nothing) trs dps)
  | isAnyNarrowingProblem p = groundRhsAllP mkHeu (p `withGoalAF` AF.init p)
  | otherwise = return p

-- ------------------------------------------------------------------------
-- A variation for use with SCCs, incorporate usable rules
-- ------------------------------------------------------------------------
{-# pff SPECIALIZE groundRhsAllP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# pff SPECIALIZE groundRhsAllP :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}

--uGroundRhsAllP :: (Lattice (AF_ id), Show id, T id :<: f, Ord id, DPMark f) => ProblemG id f -> ProblemProofG id Html f
uGroundRhsAllP mk p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then failP (GroundAll Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where heu        = mkHeu mk p -- maybe (bestHeu p) typeHeu (getTyping typ)
          results = unEmbed $ do
                  af0 <- embed $ Set.fromList $
                          foldM (\af -> findGroundAF heu pi_groundInfo af dps)
                                (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo)
                                (rules dps)
                  let utrs = mkTRS(iUsableRules trs (Just af0) (rhs <$> rules dps))
                  af1 <- embed $ Set.fromList $ invariantEV heu (dps `mappend` utrs) af0
                  let utrs' = mkTRS(iUsableRules utrs (Just af1) (rhs <$> rules dps))
                  return (af1, utrs')
          orProblems = [ proofU >>= \p' ->
                             step (GroundAll (Just (AF.restrictTo (getAllSymbols p') af))) p'
                                (AF.apply af (mkProblem Rewriting trs dps))
                        | (af,trs) <- sortBy (flip compare `on` (dpsSize.fst)) (toList results)
                        , let proofU = step UsableRulesP p (mkProblem typ trs dps)]
          dpsSize af = size (AF.apply af dps)

uGroundRhsAllP mkHeu p@(Problem (getGoalAF -> Nothing) trs dps) | isAnyNarrowingProblem p
  = uGroundRhsAllP mkHeu (p `withGoalAF` AF.init p)
uGroundRhsAllP _ p = return p

uGroundRhsOneP mk p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then failP (GroundOne Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where heu        = mkHeu mk p -- maybe (bestHeu p) typeHeu (getTyping typ)
          results = unEmbed $ do
                  af0 <- embed $ Set.fromList (
                          findGroundAF heu pi_groundInfo (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo) p
                                =<< rules dps)
                  let utrs = mkTRS(iUsableRules trs (Just af0) (rhs <$> rules dps))
                  af1 <- embed $ Set.fromList $ invariantEV heu (dps `mappend` utrs) af0
                  let utrs' = mkTRS(iUsableRules utrs (Just af1) (rhs <$> rules dps))
                  return (af1, utrs')
          orProblems = [ proofU >>= \p' ->
                             step (GroundOne (Just (AF.restrictTo (getAllSymbols p') af))) p'
                                (AF.apply af (mkProblem Rewriting trs dps))
                        | (af,trs) <- sortBy (flip compare `on` (dpsSize.fst)) (toList results)
                        , let proofU = step UsableRulesP p (mkProblem typ trs dps)]
          dpsSize af = size (AF.apply af dps)


uGroundRhsOneP mkHeu p@(Problem (getGoalAF -> Nothing) trs dps) | isAnyNarrowingProblem p
  = uGroundRhsOneP mkHeu (p `withGoalAF` AF.init p)
uGroundRhsOneP _ p = return p

-- ------------------------------------------------------------------
-- This is the AF processor described in
-- "Termination of Narrowing via Termination of Narrowing" (G.vidal)
-- ------------------------------------------------------------------
-- The only difference is that we talk of 'sound' AFs instead of 'safe'
-- Soundness is a syntactic condition whereas safeness is not.
-- That is, we simply filter all the unbound parameters out,
-- and no extra vars inserted by pi.
-- We still assume constructor substitutions and use the AF_rhs trick

-- NOTE: For now assume that this processor is unsound. The AF_rhs trick does not work well.
--       Some extra conditions are needed which I haven't identified yet.

safeAFP :: (Show id) => ProblemG id f -> ProblemProofG id Html f
safeAFP p@(Problem (getGoalAF -> Just af) trs dps@TRS{}) = assert (isSoundAF af p) $
  step (SafeAFP (Just af)) p (AF.apply af $ Problem Rewriting trs dps)
safeAFP p = return p

{-
mkBNDPProblem_rhs x@(FromAF af (Just typs)) trs = mkGoalProblem_rhs (const $ typeHeu typs) x $ mkProblem BNarrowing trs (tRS $ getPairs trs)
mkBNDPProblem_rhs x trs = mkGoalProblem_rhs bestHeu x $ mkProblem BNarrowing trs (tRS $ getPairs trs)

mkGoalProblem_rhs = mkGoalProblem' invariantEV_rhs
-}
-- -----------
-- Testing
-- -----------
{-
append  = term3 "append"
cons    = term2 ":"
nil     = constant "nil"
true    = constant "true"
xx      = var 3
yy      = var 4
zz      = var 5

(+:)    = term2 "add"
(*:)    = term2 "mul"
z       = constant "0"
s       = term1 "s"

peano_trs = mkTRS [z +: x :-> x, s x +: y :-> s(x +: y)]
mul_trs   = mkTRS [z *: x :-> z, s x *: y :-> (x *: y) +: y] `mappend` peano_trs

--append_trs :: TRS Identifier
append_trs = mkTRS
             [ append nil x x :-> true,
               append (cons x xx)  yy (cons x zz) :-> append xx yy zz]
-}


#ifdef DEBUG
instance Observable Id   where observer = observeBase
instance Observable Mode where observer = observeBase
#endif