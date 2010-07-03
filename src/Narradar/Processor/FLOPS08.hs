{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}

module Narradar.Processor.FLOPS08 where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad hiding (join)
import Data.Bifunctor
import Data.Maybe
import Data.Monoid
import Data.Foldable (Foldable, toList)
import Data.Map (Map)
import Data.Traversable (Traversable)
import qualified Data.Set as Set
import Lattice

import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Constraints.VariableCondition
import Narradar.Processor.PrologProblem hiding (SKTransformProof)
import Narradar.Types.Goal
import Narradar.Types.ArgumentFiltering (AF_, ApplyAF, PolyHeuristic, Heuristic, MkHeu(..), mkHeu, isSoundAF)
import Narradar.Types as Narradar
import Narradar.Types.Problem.NarrowingGoal as NarrowingGoal
import Narradar.Types.Problem.InitialGoal as IG
import Narradar.Utils

import qualified Data.Map as Map
import qualified Narradar.Types.ArgumentFiltering as AF

import Debug.Hood.Observe

import Prelude hiding (pi)



-- -------------------------------------------------------------------------
-- Transforms a narrowing problem into a rewriting problem (FLOPS'08 Vidal)
-- -------------------------------------------------------------------------

instance Pretty id => Pretty (NarrowingGoalToRewritingProof id) where
    pPrint NarrowingGoalToRewritingFail = text "Failed to find a safe argument filtering"

    pPrint (NarrowingGoalToRewritingProof af) = text "Termination of the following rewriting DP problem implies" <+>
                                               text "termination of the original problem [FLOPS08]." $$
                                               text "The argument filtering used is:" $$
                                               pPrint af

data ComputeSafeAF heu = ComputeSafeAF (MkHeu heu)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id
         ,DPSymbol id, Ord id, Pretty id
         ,PolyHeuristic heu id, Lattice (AF_ id)
         ,Info info (NarrowingGoalToRewritingProof id)
         ) =>
    Processor info (ComputeSafeAF heu)
              (NProblem (InitialGoal (TermF id) Narrowing) id)
              (NProblem (NarrowingGoal id) id)

  where
  applySearch (ComputeSafeAF mk) p
    | null orProblems = [dontKnow (NarrowingGoalToRewritingFail :: NarrowingGoalToRewritingProof id) p]
    | otherwise = map return orProblems
   where
     orProblems = do
       let heu = mkHeu mk p
       Abstract g <- fmap2 termToGoal (IG.goals p)
       let p'  = mkDerivedDPProblem (narrowingGoal g) p
       af' <-  Set.toList $ invariantEV heu p (NarrowingGoal.pi p')
       return p'{pi=af'}

data InferAF = InferAF
instance (Observable id, Ord id, Pretty id, Show id, DPSymbol id
         ) => Processor info InferAF
              (NProblem (InitialGoal (TermF id) Narrowing) id)
              (NProblem (NarrowingGoal id) id)
 where
  apply InferAF p = mprod [return (mkDerivedDPProblem (narrowingGoal' g piDP) p)
                             | Abstract g <- fmap2 termToGoal (IG.goals p)
                             , let pi = inferAF (getR p) (bimap unmarkDPSymbol id g)
                                   piDP = AF.mapSymbols markDPSymbol pi `mappend` pi ]

data NarrowingGoalToRewriting heu = NarrowingGoalToRewriting (MkHeu heu)
instance (t   ~ TermF id
         ,v   ~ Var
         ,trs ~ NTRS id
         ,HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         ,ICap t v (typ, trs), IUsableRules t v typ trs
         ,PolyHeuristic heu id, Lattice (AF_ id), Ord id, Pretty id
         ,MkDPProblem typ (NTRS id), Traversable (Problem typ)
         ,ApplyAF (NProblem typ id)
         ,Info info (NarrowingGoalToRewritingProof id)
         ) =>
    Processor info (NarrowingGoalToRewriting heu)
              (NProblem (MkNarrowingGoal id typ) id)
              (NProblem typ id)
  where
  applySearch (NarrowingGoalToRewriting mk) p
    | null orProblems = [dontKnow (NarrowingGoalToRewritingFail :: NarrowingGoalToRewritingProof id) p]
    | otherwise = orProblems
   where
     orProblems = do
       let heu = mkHeu mk p
           base_p = getFramework (getBaseProblem p)
       af' <-  Set.toList $ invariantEV heu p (NarrowingGoal.pi p)
       let p' = mkDerivedDPProblem base_p p
       return $ singleP (NarrowingGoalToRewritingProof af') p (AF.apply af' p')

data NarrowingGoalToRewritingProof id where
    NarrowingGoalToRewritingProof :: AF_ id -> NarrowingGoalToRewritingProof id
    NarrowingGoalToRewritingFail  :: NarrowingGoalToRewritingProof id


-- ----------------------
-- Binding Time Analysis
-- ----------------------
type Division id = Map id [Mode]
type DivEnv      = Map Int Mode

instance Lattice Mode where
    join G G = G
    join _ _ = V
    meet V V = V
    meet _ _ = G
    top      = V
    bottom   = G

instance Lattice [Mode] where
    meet     = zipWith meet
    join     = zipWith Lattice.join
    top      = repeat top
    bottom   = repeat Lattice.bottom

instance Ord id => Lattice (Division id) where
    meet   = Map.unionWith meet
    join   = Map.unionWith  join
    bottom = Map.empty
    top    = Map.empty

instance Lattice DivEnv where
    meet   = Map.unionWith meet
    join   = Map.unionWith  join
    bottom = Map.empty
    top    = Map.empty


inferAF :: (Observable id, Ord id, Show id) => NTRS id -> Goal id -> AF_ id
inferAF trs = divisionToAF . computeDivision trs
  where
   divisionToAF div = AF.fromList
                      [ (f, ii) | (f, mm) <- Map.toList div
                                , let ii = [ i | (i, G)  <- zip [1..] mm]
                      ]

-- | Receives an initial goal (its modes) and a TRS and returns a Division
--computeDivision,computeDivisionL :: (Identifier ~ id, TRSC f, T id :<: f, DPMark f id) => NarradarTRS id f -> Goal -> Division id
computeDivision :: (Observable id, Ord id, Show id) =>
                   NTRS id -> Goal id -> Division id
computeDivision  = computeDivision_ e

-- | Receives an initial goal (its modes) and a TRS and returns a Division
--computeDivision :: (Identifier ~ id, TRSC f, T id :<: f) => T id Mode -> TRS id f -> Division id
computeDivision_ e trs (Goal id mm)
  = Map.singleton id mm `meet` fixEq go div0
  where
    sig  = getSignature trs

--    div0 :: Division Identifier
    div0 = Map.fromList $
             (id,mm)
           : [(f,replicate ar G)
                  | (f,ar) <- Map.toList (Map.delete id $ definedSymbols sig)]

--    go :: Division Identifier -> Division Identifier
    go = observe "iteration" go'
    go' div = Map.mapWithKey (\f b ->
             lub (b : [ bv trs f (e f rule div) div r
                       | rule@(l:->r) <- rules trs])) div


e _g (l :-> r) div
 | Just f <- rootSymbol l
 , tt     <- directSubterms l
 = let mydiv = fromMaybe (error "FLOPS08.e") (Map.lookup f div) in
   assert (length tt == length mydiv)
   Map.fromListWith meet (
   [ (uniqueId v, V) | v <- Set.toList (getVars r `Set.difference` getVars l)] ++
   [ (uniqueId v, m) | (vv,m) <- map (toList.getVars) tt `zip` mydiv, v <- vv])

bv,bv' :: (SignatureId trs ~ id, HasSignature trs
          ,Observable trs, Observable id, Ord id, Show id
          ) => trs -> id -> DivEnv -> Division id -> TermN id -> [Mode]
bv = bv' -- observe "bv" bv'
bv' trs g rho div t@(rootSymbol -> Just f)
  = if f /= g then bt else bt `join` (be <$> tt)
     where
       tt = directSubterms t
       bt = lub (bv trs g rho div <$> tt)
--       be = observe "be" be'
       be (Pure v) = fromMaybe err (Map.lookup (uniqueId v) rho)
         where err = error $ "be: variable " ++ show v ++ " not in rho (" ++ show rho ++ ")"
       be t
        | Just f <- rootSymbol t
        , tt <- directSubterms t
                 -- note that this filters more than the algorithm in the paper
        = let ii = [ i | let Just modes = Map.lookup f div, (i,G) <- zip [1..] modes] in
          if f `Set.member` getDefinedSymbols trs
            then lub (be <$> selectSafe "FLOPS08 bv" (map pred ii) tt)
            else lub (be <$> tt)

bv' trs g _ _ t = replicate (getArity trs g) G


-- | Returns an AF which filters ground arguments from the TRS and also from the DPs.
divToAFfilterInputs p div = AF.init p `mappend`
                            AF.fromList (concat [ [(f, outputs ), (markDPSymbol f, outputs)]
                                                | (f,modes) <- Map.toList div
                                                , let outputs = [ i | (i,m) <- zip [1..] modes, m == V]])

fixEq f = go where
  go x = case f x of
              y | y == x    -> x
                | otherwise -> go y