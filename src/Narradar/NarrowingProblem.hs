{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, ViewPatterns, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}


module Narradar.NarrowingProblem (
     findGroundAF,
     groundRhsOneP, groundRhsAllP, uGroundRhsAllP, uGroundRhsOneP,
     safeAFP) where

import Control.Applicative
import Control.Exception
import Control.Monad hiding (join, mapM)
import Control.Monad.Writer(execWriter, execWriterT, MonadWriter(..), lift)
import Control.Monad.State (evalState, evalStateT, modify, MonadState(..))
import qualified Control.RMonad as R
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

import Narradar.ArgumentFiltering (AF_, PolyHeuristicN, HeuristicN, MkHeu, mkHeu)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPairs
import Narradar.Proof
import Narradar.Utils
import Narradar.Types as Narradar
import Narradar.ExtraVars
import Narradar.UsableRules
import Narradar.Aprove
import Lattice

#ifdef DEBUG
import Debug.Observe
#endif

-- ------------------------------------------------------------------------
-- This is the AF processor described in our ICLP'08 paper
-- ------------------------------------------------------------------------
groundRhsOneP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> ProblemG id v -> [m(ProblemG id v)]
groundRhsOneP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) trs dps)
  | isAnyNarrowingProblem p =
    if null orProblems
      then [failP EVProcFail p]
      else orProblems
    where heu = mkHeu mk p
          af0 = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo0
          afs = unEmbed $ do
                  af00 <- embed $ invariantEV heu p af0
                  let pi_groundInfo = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) af00
                  embed $ findGroundAF heu pi_groundInfo af0 p R.=<< Set.fromList(rules dps)
          orProblems = [ step (GroundOne (Just af)) p $
                                AF.apply af (mkProblem (correspondingRewritingStrategy typ) trs dps)
                        | af <- Set.toList afs]

groundRhsOneP mk p@(Problem typ@(getAF -> Nothing) trs dps)
  | isAnyNarrowingProblem p =
    if null orProblems then [failP EVProcFail p] else orProblems
  | otherwise = [return p]
    where heu        = mkHeu mk p
          afs        = findGroundAF heu (AF.empty p) (AF.init p) p R.=<< Set.fromList(rules dps)
          orProblems = [ step (GroundOne (Just af)) p $
                                AF.apply af (mkProblem (correspondingRewritingStrategy typ) trs dps)
                        | af <- Set.toList afs]

-- ------------------------------------------------------------------------
-- A variation for use with SCCs
-- ------------------------------------------------------------------------
groundRhsAllP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> ProblemG id v -> [m(ProblemG id v)]
groundRhsAllP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then [failP EVProcFail p]
      else orProblems
    where heu  = mkHeu mk p
          typ' = correspondingRewritingStrategy typ
          afs  = unEmbed $ do
                   af00 <- embed $ invariantEV heu p pi_groundInfo0
                   let pi_groundInfo = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) af00
                   embed $ R.foldM (\af -> findGroundAF heu pi_groundInfo af p)
                                   (AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo)
                                   (rules dps)
          orProblems = [ step (GroundAll (Just af)) p $
                                AF.apply af (mkProblem typ' trs dps)
                        | af <- Set.toList afs]

groundRhsAllP mkHeu p@(Problem (getAF -> Nothing) trs dps)
  | isAnyNarrowingProblem p = groundRhsAllP mkHeu (p `withAF` AF.init p)
  | otherwise = [return p]

-- ------------------------------------------------------------------------
-- A variation for use with SCCs, incorporate usable rules
-- ------------------------------------------------------------------------
uGroundRhsAllP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> ProblemG id v -> [m(ProblemG id v)]
uGroundRhsAllP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then [failP EVProcFail p]
      else orProblems
    where heu     = mkHeu mk p
          typ'    = correspondingRewritingStrategy typ
          results = unEmbed $ do
                  pi_groundInfo <- embed $ invariantEV heu p pi_groundInfo0
                  af0  <- embed $
                          R.foldM (\af -> findGroundAF heu pi_groundInfo af p)
                                  (AF.init p)
                                  (rules dps)
                  let utrs = mkTRS(iUsableRules trs (Just af0) (rhs <$> rules dps))
                  af1 <- embed $ invariantEV heu (dps `mappend` utrs) af0
                  let utrs' = mkTRS(iUsableRules utrs (Just af1) (rhs <$> rules dps))
                  return (af1, utrs')
          orProblems = [ proofU >>= \p' -> assert (isSoundAF af p') $
                             step (GroundAll (Just (AF.restrictTo (getAllSymbols p') af))) p'
                                (AF.apply af (mkProblem typ' trs dps))
                        | (af,trs) <- sortBy (flip compare `on` (dpsSize.fst)) (toList results)
                        , let proofU = step UsableRulesP p (mkProblem typ trs dps)]
          dpsSize af = size (AF.apply af dps)

uGroundRhsAllP mkHeu p@(Problem (getAF -> Nothing) trs dps) | isAnyNarrowingProblem p
  = uGroundRhsAllP mkHeu (p `withAF` AF.init p)
uGroundRhsAllP _ p = [return p]

uGroundRhsOneP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> ProblemG id v -> [m(ProblemG id v)]
uGroundRhsOneP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then [failP EVProcFail p]
      else orProblems
    where heu     = mkHeu mk p
          typ'    = correspondingRewritingStrategy typ
          results = unEmbed $ do
                  af00 <- embed $ invariantEV heu p pi_groundInfo0
                  let pi_groundInfo = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) af00
                  af0  <- embed $
                          findGroundAF heu af00 pi_groundInfo p R.=<< Set.fromList(rules dps)
                  let utrs = mkTRS(iUsableRules trs (Just af0) (rhs <$> rules dps))
                  af1 <- let rr = dps `mappend` utrs in
                         embed $ invariantEV heu rr (AF.restrictTo (getAllSymbols rr) af0)
                  let utrs' = mkTRS(iUsableRules utrs (Just af1) (rhs <$> rules dps))
                  return (af1, utrs')

          orProblems = [ proofU >>= \p' -> assert (isSoundAF af p') $
                             step (GroundOne (Just (AF.restrictTo (getAllSymbols p') af))) p'
                                (AF.apply af (mkProblem typ' trs dps))
                        | (af,trs) <- sortBy (flip compare `on` (dpsSize.fst)) (toList results)
                        , let proofU = step UsableRulesP p (mkProblem typ trs dps)]
          dpsSize af = size (AF.apply af dps)


uGroundRhsOneP mkHeu p@(Problem (getAF -> Nothing) trs dps) | isAnyNarrowingProblem p
  = uGroundRhsOneP mkHeu (p `withAF` AF.init p)
uGroundRhsOneP _ p = [return p]

-- ------------------------------------------------------------------
-- This is the infinitary constructor rewriting AF processor described in
-- "Termination of Logic Programs ..." (Schneider-Kamp et al)
-- ------------------------------------------------------------------

safeAFP :: (Show id, Ord id, Ppr id, Lattice (AF_ id), PolyHeuristicN heu id, MonadFree ProofF m, v ~ Var) =>
           MkHeu heu -> ProblemG id v -> [m(ProblemG id v)]
safeAFP mk p@(Problem typ@(getAF -> Just af) trs dps) = do
       let heu = mkHeu mk p
       af' <-  toList $ invariantEV heu (rules p) af
       return $ step (SafeAFP (Just af')) p
                  (AF.apply af' $ mkProblem typ' (tRS $ iUsableRules trs (Just af) (rhs <$> rules dps)) dps)
  where typ' = correspondingRewritingStrategy typ

safeAFP _ p = [return p]

-- ---------------
-- building blocks
-- ---------------
-- | Takes a heuristic, an af with groundness information, an af to use as starting point, a problem and a rule,
findGroundAF :: (Ord id, Ppr id, Lattice (AF_ id), v ~ Var) =>
                HeuristicN id
             -> AF_ id         -- ^ Groundness information
             -> AF_ id         -- ^ the argument filtering to constrain
             -> ProblemG id v
             -> RuleN id v     -- ^ the rule to make ground
             -> Set (AF_ id)
findGroundAF heu pi_groundInfo af0 p@(Problem _ trs dps) (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu dps
            where
              mkGround t = cutWith heu (af0 `mappend` pi_c) t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)] \\\
                                [note v | v <- subterms (AF.apply pi_d $ annotateWithPos t)]

              (pi_c,pi_d) = AF.splitCD p pi_groundInfo

#ifdef DEBUG
instance Observable Id   where observer = observeBase
instance Observable Mode where observer = observeBase
#endif