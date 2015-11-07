{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, ViewPatterns, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
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

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe

data NarrowingToRewritingICLP08 heu (info :: * -> *) =
          NarrowingToRewritingICLP08 (MkHeu heu)
        | NarrowingToRewritingICLP08_SCC (MkHeu heu)

type instance InfoConstraint (NarrowingToRewritingICLP08 heu info) = info


instance ( PolyHeuristic heu id, Lattice (AF_ id)
         , Info info (Problem Narrowing (NTRS id))
         , Info info (Problem Rewriting (NTRS id))
         , Info info (UsableRulesProof (TermN id))
         , Info info (NarrowingToRewritingProof id)
         , FrameworkProblemN base id
         , FrameworkProblemN (MkNarrowing base) id
         , HasSignature (Problem (MkNarrowing base) (NTRS id))
         ) =>
    Processor (NarrowingToRewritingICLP08 heu info) (Problem (MkNarrowing base) (NTRS id) ) where
  type Typ (NarrowingToRewritingICLP08 heu info) (Problem (MkNarrowing base) (NTRS id)) = base
  type Trs (NarrowingToRewritingICLP08 heu info) (Problem (MkNarrowing base) (NTRS id)) = NTRS id
  applySearchO o (NarrowingToRewritingICLP08 mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p
          af         = AF.init u_p
          afs        = findGroundAF heu af u_p R.=<< Set.fromList(rules dps)
          orProblems = [ usableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (getBaseProblem p')
                        | af <- Set.toList afs]

  applySearchO o (NarrowingToRewritingICLP08_SCC mk) p
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where (trs, dps) = (getR p, getP p)
          heu        = mkHeu mk p
          u_p        = iUsableRules p
          afs        = R.foldM (\af -> findGroundAF heu af u_p) (AF.init u_p) (rules dps)
          orProblems = [ usableRulesProof p u_p >>= \ p' ->
                         singleP (NarrowingToRewritingICLP08Proof af) p' $
                                AF.apply af (getBaseProblem p')
                        | af <- Set.toList afs]


instance ( HasSignature (NProblem base id)
         , id ~ Family.Id (NProblem base id)
         , PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id, Pretty (TermN id)
         , ApplyAF (TermN id)
         , Info info (NProblem (MkNarrowingGoal id base) id)
         , Info info (NProblem base id)
         , Info info (NarrowingToRewritingProof id)
         , MkDPProblem base (NTRS id), Traversable (Problem base)
         , NUsableRules base id
         , NCap base id
         , Eq base
         , Observable base, Observable id
         ) =>
    Processor (NarrowingToRewritingICLP08 heu info)
              (NProblem (MkNarrowingGoal id base) id)
 where
  type Typ (NarrowingToRewritingICLP08 heu info) (NProblem (MkNarrowingGoal id base) id) = base
  type Trs (NarrowingToRewritingICLP08 heu info) (NProblem (MkNarrowingGoal id base) id) = NTRS id

bad :: forall id base info heu .
       (Info info (NarrowingToRewritingProof id)
       ,Info info (NProblem (MkNarrowingGoal id base) id)
       ,Lattice (AF_ id)
       ,PolyHeuristic heu id
       ,FrameworkProblemN base id
       ,HasSignature (NProblem base id)
       ) =>
    NarrowingToRewritingICLP08 heu info -> NProblem (MkNarrowingGoal id base) id -> [Proof info (NProblem base id)]
bad (NarrowingToRewritingICLP08 mk) p@(getFramework -> NarrowingGoal _ pi_groundInfo0 _ base)
    | null orProblems = [dontKnow (NarrowingToRewritingICLP08Fail :: NarrowingToRewritingProof id) p]
    | otherwise = orProblems
    where heu = mkHeu mk p
          af0 = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) pi_groundInfo0
          afs = unEmbed $ do
                  af00 <- embed $ invariantEV heu (rules p) af0
                  let pi_groundInfo = AF.init p `mappend` AF.restrictTo (getConstructorSymbols p) af00
                  embed $ findGroundAF' heu pi_groundInfo af0 p R.=<< Set.fromList(rules $ getP p)
          orProblems = [ singleP (NarrowingToRewritingICLP08Proof af) p $
                                AF.apply af (mkDerivedDPProblem base p)
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
findGroundAF :: ( FrameworkId id, Lattice (AF_ id)
                , Foldable (Problem typ)
                , MkDPProblem typ (NTRS id)
                , HasSignature (NProblem typ id)
                ) => Heuristic id -> AF_ id -> NProblem typ id -> RuleN id -> Set (AF_ id)
findGroundAF heu af0 p (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu (rules p)
            where
              mkGround t = cutWith heu af0 t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)]


-- | Takes a heuristic, an af with groundness information, an af to use as starting point, a problem and a rule,
findGroundAF' :: ( IsDPProblem typ
                 , FrameworkId id, Lattice (AF_ id)
                 , Foldable (Problem typ)
                 , HasSignature (NProblem typ id)
                 ) =>
                Heuristic id
             -> AF_ id         -- ^ Groundness information
             -> AF_ id         -- ^ the argument filtering to constrain
             -> NProblem typ id
             -> RuleN id     -- ^ the rule to make ground
             -> Set (AF_ id)
findGroundAF' heu pi_groundInfo af0 p (_:->r)
  | isVar r = Set.empty
  | otherwise = mkGround r R.>>= invariantEV heu (rules p)
            where
              mkGround t = cutWith heu (af0 `mappend` pi_c) t varsp -- TODO Fix: cut one at a time
                  where varsp = [noteV v | v <- vars (annotateWithPos t)] \\
                                [note v | v <- subterms (AF.apply pi_d $ annotateWithPos t)]

              (pi_c,pi_d) = AF.splitCD p pi_groundInfo
