{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}

module NarrowingProblem (
     mkGoalProblem, mkGoalProblem_rhs,
     groundRhsOneP, groundRhsAllP,
     safeAFP,
     MkGoalProblem(..)) where

import Control.Applicative
import Control.Exception
import Control.Monad hiding (join, mapM)
import Control.Monad.Free hiding (note)
import Control.Monad.Writer(execWriter, execWriterT, MonadWriter(..), lift)
import Control.Monad.State (evalState, evalStateT, modify, MonadState(..))
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (intersect, (\\))
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)
import Data.Traversable
import Text.XHtml (toHtml, Html)
import Prelude hiding (mapM)

import Debug.Observe
import Debug.Trace

import ArgumentFiltering (AF_,AF, LabelledAF, Heuristic, bestHeu, typeHeu)
import qualified ArgumentFiltering as AF
import DPairs
import Proof
import Utils
import Types
import TRS
import Lattice
import ExtraVars
import Language.Prolog.TypeChecker

#ifdef DEBUG
import Debug.Trace
#else
trace _ x = x
#endif

data MkGoalProblem id = FromGoal Goal (Maybe TypeAssignment) | FromAF (AF_ id) (Maybe TypeAssignment) | AllTerms

mkGoalProblem :: (DPMark f id, Lattice (AF_ id), Bottom :<: f) => MkGoalProblem id -> ProblemG id f -> ProblemProofG id Html f
mkGoalProblem (FromGoal goal typ) p = mkGoalProblem (FromAF (mkGoalAF p goal) typ) p
   where
    mkGoalAF :: (DPSymbol id, Show id, Ord id, SignatureC sig id) => sig -> Goal -> AF_ id
    mkGoalAF p (T goal modes) = AF.init p `mappend`
                   let pp = [ i | (i,m) <- zip [1..] modes, m == G]
                   in AF.fromList [(f,pp) | (f,pp) <- [(functionSymbol goal, pp), (dpSymbol goal, pp)]
                                          ]
mkGoalProblem (FromAF goalAF Nothing) p@(Problem (getGoalAF -> Nothing) trs dps) = do
--    p' <- evProcessor p
    let extendedAF = goalAF `mappend` extendAFToTupleSymbols goalAF
    let orProblems = [(p `withGoalAF` af) | af <- invariantEV (bestHeu p) p (extendedAF)]
    assert (not $ null orProblems) $ msum (map return orProblems)

mkGoalProblem (FromAF goalAF (Just typing)) p@(Problem (getGoalAF -> Nothing) trs dps) = do
--    p' <- evProcessor p
    let extendedAF = goalAF `mappend` extendAFToTupleSymbols goalAF
    let orProblems = [(p `withGoalAF` af `withTyping` typing) | af <- invariantEV (typeHeu typing) p (extendedAF)]
    assert (not $ null orProblems) $ msum (map return orProblems)

mkGoalProblem AllTerms p = return p

extendAFToTupleSymbols = AF.mapSymbols markDPSymbol
-- ------------------------------------------------------------------------
-- This is the AF processor described in our Dependency Pairs for Narrowing
-- ------------------------------------------------------------------------
{-# SPECIALIZE groundRhsOneP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE groundRhsOneP :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
groundRhsOneP :: (Bottom :<: f, Lattice (AF_ id), DPMark  f id) => ProblemG id f -> ProblemProofG id Html f
groundRhsOneP p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then failP (GroundOne Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where heu        = maybe (bestHeu p) typeHeu (getTyping typ)
          afs        = findGroundAF heu pi_groundInfo (AF.init p) p =<< rules dps
          orProblems = [ step (GroundOne (Just af)) p $
                                AF.apply af (mkProblem Rewriting trs dps)
                        | af <- afs]

groundRhsOneP p@(Problem (getGoalAF -> Nothing) trs dps) | isAnyNarrowingProblem p = groundRhsOneP (p `withGoalAF` AF.init p)
groundRhsOneP p = return p

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
{-# SPECIALIZE groundRhsAllP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE groundRhsAllP :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
groundRhsAllP :: (Bottom :<: f, Lattice (AF_ id), DPMark  f id) => ProblemG id f -> ProblemProofG id Html f
groundRhsAllP p@(Problem typ@(getGoalAF -> Just pi_groundInfo) trs dps) | isAnyNarrowingProblem p =
    if null orProblems
      then failP (GroundAll Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where heu        = maybe (bestHeu p) typeHeu (getTyping typ)
          afs        = foldM (\af -> findGroundAF heu pi_groundInfo af p)  (AF.init p) (rules dps)
          orProblems = [ step (GroundAll (Just af)) p $
                                AF.apply af (mkProblem Rewriting trs dps)
                        | af <- afs]

groundRhsAllP p@(Problem (getGoalAF -> Nothing) trs dps) | isAnyNarrowingProblem p = groundRhsAllP (p `withGoalAF` AF.init p)
groundRhsAllP p = return p

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
safeAFP :: (Bottom :<: f, DPMark f id) => ProblemG id f -> ProblemProofG id Html f
safeAFP p@(Problem (getGoalAF -> Just af) trs dps) = assert (isSoundAF af p) $
  step (GroundAll (Just af)) p (AF.apply_rhs p af $ Problem Rewriting trs dps)
safeAFP p = return p

mkBNDPProblem_rhs  mb_goal trs = mkGoalProblem_rhs mb_goal $ mkProblem BNarrowing trs (tRS $ getPairs trs)

mkGoalProblem_rhs (FromGoal goal typ) p = mkGoalProblem (FromAF (mkGoalAF p goal) typ) p
   where
    mkGoalAF :: (DPSymbol id, Show id, Ord id, SignatureC sig id) => sig -> Goal -> AF_ id
    mkGoalAF p (T goal modes) = AF.init p `mappend`
                   let pp = [ i | (i,m) <- zip [1..] modes, m == G]
                   in AF.fromList [(f,pp) | (f,pp) <- [(functionSymbol goal, pp), (dpSymbol goal, pp)]]
mkGoalProblem_rhs (FromAF goalAF Nothing) p@(Problem (getGoalAF -> Nothing) trs dps) = do
--    p' <- evProcessor p
    let extendedAF = goalAF `mappend` extendAFToTupleSymbols goalAF
    let orProblems = [(p `withGoalAF` af) | af <- invariantEV_rhs (bestHeu p) p (extendedAF)]
    assert (not $ null orProblems) $ msum (map return orProblems)

mkGoalProblem_rhs (FromAF goalAF (Just typing)) p@(Problem (getGoalAF -> Nothing) trs dps) = do
--    p' <- evProcessor p
    let extendedAF = goalAF `mappend` extendAFToTupleSymbols goalAF
    let orProblems = [(p `withGoalAF` af `withTyping` typing) | af <- invariantEV_rhs (typeHeu typing) p (extendedAF)]
    assert (not $ null orProblems) $ msum (map return orProblems)

mkGoalProblem_rhs AllTerms p = return p

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

instance Observable Identifier where observer = observeBase
instance Observable Mode where observer = observeBase
