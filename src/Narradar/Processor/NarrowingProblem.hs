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
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristic, Heuristic, MkHeu, mkHeu, isSoundAF, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.GraphViz hiding (note)
import Narradar.Processor.UsableRules
import Narradar.Types as Narradar
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Utils
import Lattice

#ifdef HOOD
import Debug.Observe
#endif

data NarrowingToRewritingICLP08 heu = NarrowingToRewritingICLP08 (MkHeu heu)
                                    | NarrowingToRewritingICLP08_SCC (MkHeu heu)


instance ( PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id, Pretty (TermN id)
         , Info info (Problem Narrowing (NTRS id))
         , Info info (Problem Rewriting (NTRS id))
         , Info info UsableRulesProof
         , Info info (NarrowingToRewritingProof id)
         ) =>
    Processor info (NarrowingToRewritingICLP08 heu) (Problem Narrowing (NTRS id) ) (Problem Rewriting (NTRS id) ) where
  applySearch (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = findGroundAF heu (AF.init u_p) u_p R.=<< Set.fromList(rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkDerivedProblem Rewriting p')
                        | af <- Set.toList afs]

  applySearch (NarrowingToRewritingICLP08_SCC mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = R.foldM (\af -> findGroundAF heu af u_p) (AF.init u_p) (rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p' $
                                AF.apply af (mkDerivedProblem Rewriting p')
                        | af <- Set.toList afs]

instance ( PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id, Pretty (TermN id)
         , Info info (NProblem CNarrowing id)
         , Info info (NProblem IRewriting id)
         , Info info (NarrowingToRewritingProof id)
         , Info info UsableRulesProof
         ) =>
    Processor info (NarrowingToRewritingICLP08 heu) (Problem CNarrowing (NTRS id)) (Problem IRewriting (NTRS id))
 where
  applySearch (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = findGroundAF heu (AF.init u_p) u_p R.=<< Set.fromList(rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkDerivedProblem IRewriting p')
                        | af <- Set.toList afs]

  applySearch (NarrowingToRewritingICLP08_SCC mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p (rhs <$> rules dps)
          afs        = R.foldM (\af -> findGroundAF heu af u_p) (AF.init u_p) (rules dps)
          orProblems = [ singleP UsableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p' $
                                AF.apply af (mkDerivedProblem IRewriting p')
                        | af <- Set.toList afs]


instance ( HasSignature (NProblem typ0 id), id ~ SignatureId (NProblem typ0 id)
         , PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id, Pretty (TermN id)
         , ApplyAF (NProblem typ0 id)
         , Info info (NProblem (MkNarrowingGoal id typ0) id)
         , Info info (NProblem typ0 id)
         , Info info (NarrowingToRewritingProof id)
         , MkDPProblem typ0 (NTRS id), Traversable (Problem typ0)
         , NUsableRules id (typ0, NTRS id)
         , NCap id (typ0, NTRS id)
         ) =>
    Processor info (NarrowingToRewritingICLP08 heu)
                   (NProblem (MkNarrowingGoal id typ0) id)
                   (NProblem typ0 id)
 where
  applySearch (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where heu = mkHeu mk p
          NarrowingGoal _ pi_groundInfo0 typ0 = getProblemType p
          af0 = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo0
          afs = unEmbed $ do
                  af00 <- embed $ invariantEV heu p af0
                  let pi_groundInfo = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) af00
                  embed $ findGroundAF' heu pi_groundInfo af0 p R.=<< Set.fromList(rules $ getP p)
          orProblems = [ singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkDerivedProblem typ0 p)
                        | af <- Set.toList afs]


-- -----------
-- Proofs
-- -----------

data NarrowingToRewritingProof id where
    NarrowingToRewritingICLP08Proof :: AF_ id -> NarrowingToRewritingProof id
    NarrowingToRewritingICLP08Fail  :: NarrowingToRewritingProof id

instance Pretty id => Pretty (NarrowingToRewritingProof id) where
    pPrint NarrowingToRewritingICLP08Fail = text "Failed to find an argument filtering that satisfies" $$
                                         text "the one pair with a ground right hand side condition."
    pPrint (NarrowingToRewritingICLP08Proof af) = text "Termination of the following rewriting DP problem" $$
                                               text "implies termination of the original problem." $$
                                               text "The following argument filtering was used:" $$
                                               pPrint af


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
findGroundAF' :: ( IsDPProblem typ, HasSignature (Problem typ (NarradarTRS t Var))
                 , Traversable t, HasId t, ApplyAF (Term t Var), Ord (Term t Var)
                 , id ~ TermId t, id ~ AFId (Term t Var), id ~ SignatureId (Problem typ (NarradarTRS t Var))
                 , Ord id, Pretty id, Lattice (AF_ id), Foldable (Problem typ)
                 , ApplyAF (Problem typ (NarradarTRS t Var))
                 , ApplyAF (Term (WithNote1 Position t) (WithNote Position Var))
                 , AFId (Term (WithNote1 Position t) (WithNote Position Var)) ~ id
                 ) =>
                Heuristic id
             -> AF_ id         -- ^ Groundness information
             -> AF_ id         -- ^ the argument filtering to constrain
             -> Problem typ (NarradarTRS t Var)
             -> Rule t Var     -- ^ the rule to make ground
             -> Set (AF_ id)
findGroundAF' heu pi_groundInfo af0 p (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu p
            where
              mkGround t = cutWith heu (af0 `mappend` pi_c) t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)] \\\
                                [note v | v <- subterms (AF.apply pi_d $ annotateWithPos t)]

              (pi_c,pi_d) = AF.splitCD p pi_groundInfo

#ifdef HOOD
instance Observable Id   where observer = observeBase
#endif
