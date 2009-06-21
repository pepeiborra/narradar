{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, ViewPatterns, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}


module Narradar.Processor.NarrowingProblem (
     findGroundAF,
     groundRhsOneP, groundRhsAllP, uGroundRhsAllP, uGroundRhsOneP,
     safeAFP) where

import Control.Applicative
import Control.Exception
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.List ( (\\), sortBy)
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import Prelude hiding (mapM, pi)

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristicN, HeuristicN, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework.Proof
import Narradar.Utils
import Narradar.Types as Narradar
import Lattice

#ifdef DEBUG
import Debug.Observe
#endif

-- ------------------------------------------------------------------------
-- This is the AF processor described in our ICLP'08 paper
-- ------------------------------------------------------------------------
groundRhsOneP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> Problem id v -> [m(Problem id v)]
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
                  MkHeu heu -> Problem id v -> [m(Problem id v)]
groundRhsAllP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) _ dps) | isAnyNarrowingProblem p =
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
                                AF.apply af (setTyp typ' p)
                        | af <- Set.toList afs]

groundRhsAllP mkHeu p@(Problem (getAF -> Nothing) _ _)
  | isAnyNarrowingProblem p = groundRhsAllP mkHeu (p `withAF` AF.init p)
  | otherwise = [return p]

-- ------------------------------------------------------------------------
-- A variation for use with SCCs, incorporate usable rules
-- ------------------------------------------------------------------------
uGroundRhsAllP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> Problem id v -> [m(Problem id v)]
uGroundRhsAllP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) _ dps) | isAnyNarrowingProblem p =
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
                  let u_p = iUsableRules p (Just af0) (rhs <$> rules dps)
                  af1 <- embed $ invariantEV heu u_p af0
                  let u_p' = iUsableRules u_p (Just af1) (rhs <$> rules dps)
                  return (af1, u_p')
          orProblems = [ proofU >>= \p' -> assert (isSoundAF af p') $
                             step (GroundAll (Just (AF.restrictTo (getAllSymbols p') af))) p'
                                (AF.apply af (setTyp typ' p'))
                        | (af,p') <- sortBy (flip compare `on` (dpsSize.fst)) (Set.toList results)
                        , let proofU = step UsableRulesP p p']
          dpsSize af = size (AF.apply af dps)

uGroundRhsAllP mkHeu p@(Problem (getAF -> Nothing) _ _) | isAnyNarrowingProblem p
  = uGroundRhsAllP mkHeu (p `withAF` AF.init p)
uGroundRhsAllP _ p = [return p]

uGroundRhsOneP :: (PolyHeuristicN heu id, Lattice (AF_ id), Ppr id, Ord id, MonadFree ProofF m, v ~ Var) =>
                  MkHeu heu -> Problem id v -> [m(Problem id v)]
uGroundRhsOneP mk p@(Problem typ@(getAF -> Just pi_groundInfo0) _ dps) | isAnyNarrowingProblem p =
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
                  let u_p  = iUsableRules p   (Just af0) (rhs <$> rules dps)
                  af1 <- embed $ invariantEV heu u_p (AF.restrictTo (getAllSymbols u_p) af0)
                  let u_p' = iUsableRules u_p (Just af1) (rhs <$> rules dps)
                  return (af1, u_p')

          orProblems = [ proofU >>= \p' -> assert (isSoundAF af p') $
                             step (GroundOne (Just (AF.restrictTo (getAllSymbols p') af))) p'
                                (AF.apply af (setTyp typ' p'))
                        | (af,p') <- sortBy (flip compare `on` (dpsSize.fst)) (Set.toList results)
                        , let proofU = step UsableRulesP p p']
          dpsSize af = size (AF.apply af dps)


uGroundRhsOneP mkHeu p@(Problem (getAF -> Nothing) _ _) | isAnyNarrowingProblem p
  = uGroundRhsOneP mkHeu (p `withAF` AF.init p)
uGroundRhsOneP _ p = [return p]

-- ------------------------------------------------------------------
-- This is the infinitary constructor rewriting AF processor described in
-- "Termination of Logic Programs ..." (Schneider-Kamp et al)
-- ------------------------------------------------------------------

safeAFP :: (Ord id, Ppr id, Lattice (AF_ id), PolyHeuristicN heu id, MonadFree ProofF m, v ~ Var) =>
           MkHeu heu -> Problem id v -> [m(Problem id v)]
safeAFP mk p@(Problem typ@(getAF -> Just af) _ dps) = do
       let heu = mkHeu mk p
       af' <-  Set.toList $ invariantEV heu p af
       let p' = iUsableRules (setTyp typ' p) (Just af) (rhs <$> rules dps)
       return $ step (SafeAFP (Just af')) p (AF.apply af' p')
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
             -> Problem id v
             -> RuleN id v     -- ^ the rule to make ground
             -> Set (AF_ id)
findGroundAF heu pi_groundInfo af0 p@(Problem _ _ dps) (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu dps
            where
              mkGround t = cutWith heu (af0 `mappend` pi_c) t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)] \\\
                                [note v | v <- subterms (AF.apply pi_d $ annotateWithPos t)]

              (pi_c,pi_d) = AF.splitCD p pi_groundInfo

#ifdef DEBUG
instance Observable Id   where observer = observeBase
#endif
