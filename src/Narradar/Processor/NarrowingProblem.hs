{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, ViewPatterns, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}


module Narradar.Processor.NarrowingProblem where
import Control.Applicative
import Control.Exception
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.List ( (\\), sortBy)
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import Prelude hiding (mapM, pi)

import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristicN, HeuristicN, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.GraphViz hiding (note)
import Narradar.Processor.UsableRules
import Narradar.Types as Narradar
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Utils
import Lattice

#ifdef DEBUG
import Debug.Observe
#endif

data NarrowingToRewritingICLP08 heu = NarrowingToRewritingICLP08 (MkHeu heu)
                                    | NarrowingToRewritingICLP08_SCC (MkHeu heu)


instance (PolyHeuristicN heu id, Lattice (AF_ id), Ord id, Ppr id) =>
    Processor (NarrowingToRewritingICLP08 heu) (NarradarTRS id Var) Narrowing Rewriting where
  applySearch (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [failP NarrowingToRewritingICLP08Fail p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = findGroundAF heu (AF.init u_p) u_p R.=<< Set.fromList(rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkNewProblem Rewriting p')
                        | af <- Set.toList afs]

  applySearch (NarrowingToRewritingICLP08_SCC mk) p
    | null orProblems = [failP NarrowingToRewritingICLP08Fail p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = R.foldM (\af -> findGroundAF heu af u_p) (AF.init u_p) (rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p' $
                                AF.apply af (mkNewProblem Rewriting p')
                        | af <- Set.toList afs]

instance (PolyHeuristicN heu id, Lattice (AF_ id), Ord id, Ppr id) =>
    Processor (NarrowingToRewritingICLP08 heu) (NarradarTRS id Var) CNarrowing IRewriting where
  applySearch (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [failP NarrowingToRewritingICLP08Fail p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = findGroundAF heu (AF.init u_p) u_p R.=<< Set.fromList(rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkNewProblem IRewriting p')
                        | af <- Set.toList afs]

  applySearch (NarrowingToRewritingICLP08_SCC mk) p
    | null orProblems = [failP NarrowingToRewritingICLP08Fail p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = R.foldM (\af -> findGroundAF heu af u_p) (AF.init u_p) (rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p' $
                                AF.apply af (mkNewProblem IRewriting p')
                        | af <- Set.toList afs]


instance (p ~ NarradarProblem (NarrowingGoalGen id typ0) id
         ,PolyHeuristicN heu id, Lattice (AF_ id), Ord id, Ppr id
         ,IsDPProblem typ0, ProblemInfo p, Traversable (DPProblem typ0)) =>
    Processor (NarrowingToRewritingICLP08 heu) (NarradarTRS id Var) (NarrowingGoalGen id typ0) typ0 where
  applySearch (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [failP NarrowingToRewritingICLP08Fail p]
    | otherwise = orProblems
    where heu = mkHeu mk p
          NarrowingGoal pi_groundInfo0 typ0 = getProblemType p
          af0 = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo0
          afs = unEmbed $ do
                  af00 <- embed $ invariantEV heu p af0
                  let pi_groundInfo = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) af00
                  embed $ findGroundAF' heu pi_groundInfo af0 p R.=<< Set.fromList(rules $ getP p)
          orProblems = [ singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkNewProblem typ0 p)
                        | af <- Set.toList afs]


-- -----------
-- Proofs
-- -----------

data NarrowingToRewritingProof id where
    NarrowingToRewritingICLP08Proof :: AF_ id -> NarrowingToRewritingProof id
    NarrowingToRewritingICLP08Fail  :: NarrowingToRewritingProof ()

instance Ppr id => Ppr (NarrowingToRewritingProof id) where
    ppr NarrowingToRewritingICLP08Fail = text "Failed to find an argument filtering that satisfies" $$
                                         text "the one pair with a ground right hand side condition."
    ppr (NarrowingToRewritingICLP08Proof af) = text "Termination of the following rewriting DP problem" $$
                                               text "implies termination of the original problem." $$
                                               text "The following argument filtering was used:" $$
                                               ppr af

instance Ppr id =>  ProofInfo (NarrowingToRewritingProof id)


-- ---------------
-- building blocks
-- ---------------
findGroundAF heu af0 p (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu p
            where
              mkGround t = cutWith heu af0 t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)]


-- | Takes a heuristic, an af with groundness information, an af to use as starting point, a problem and a rule,
findGroundAF' :: (IsDPProblem typ, HasSignature (NarradarProblem typ id), Ord id, Ppr id, Lattice (AF_ id), Foldable (DPProblem typ)) =>
                HeuristicN id
             -> AF_ id         -- ^ Groundness information
             -> AF_ id         -- ^ the argument filtering to constrain
             -> NarradarProblem typ id
             -> RuleN id Var     -- ^ the rule to make ground
             -> Set (AF_ id)
findGroundAF' heu pi_groundInfo af0 p (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu p
            where
              mkGround t = cutWith heu (af0 `mappend` pi_c) t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)] \\\
                                [note v | v <- subterms (AF.apply pi_d $ annotateWithPos t)]

              (pi_c,pi_d) = AF.splitCD p pi_groundInfo

#ifdef DEBUG
instance Observable Id   where observer = observeBase
#endif
