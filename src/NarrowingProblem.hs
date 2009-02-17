{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, TypeSynonymInstances #-}

module NarrowingProblem (
     mkNDPProblem,
     mkBNDPProblem,
     mkLBNDPProblem,
     afProcessor,
     MkProblem(..), mkGoalProblem
             ) where

import Control.Applicative
import Control.Exception
import Control.Monad hiding (join)
import Control.Monad.Free hiding (note)
import Control.Monad.Writer(execWriter, execWriterT, MonadWriter(..), lift)
import Control.Monad.State (evalState, evalStateT, modify, MonadState(..))
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (intersect)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)
import Text.XHtml (toHtml, Html)

import Debug.Observe
import Debug.Trace

import ArgumentFiltering (AF_,AF, LabelledAF, Heuristic, bestHeu, allInner)
import qualified ArgumentFiltering as AF
import DPairs
import Proof
import Utils
import Types
import TRS
import Lattice
import ExtraVars

import Debug.Trace

data MkProblem id = FromGoal Goal | FromAF (AF_ id) | AllTerms

mkNDPProblem   mb_goal trs = mkGoalProblem mb_goal $ mkProblem Narrowing   trs (tRS $ getNPairs trs)
mkBNDPProblem  mb_goal trs = mkGoalProblem mb_goal $ mkProblem BNarrowing  trs (tRS $ getPairs trs)
mkLBNDPProblem mb_goal trs = mkGoalProblem mb_goal $ mkProblem LBNarrowing trs (tRS $ getPairs trs)

mkGoalProblem (FromGoal goal) p = mkGoalProblem (FromAF$ mkGoalAF p goal) p
   where
    mkGoalAF :: (DPSymbol id, Show id, Ord id, SignatureC sig id) => sig -> Goal -> AF_ id
    mkGoalAF p (T goal modes) = AF.init p `mappend`
                   let pp = [ i | (i,m) <- zip [1..] modes, m == G]
                   in AF.fromList [(f,pp) | (f,pp) <- [(functionSymbol goal, pp), (dpSymbol goal, pp)]
                                          ]
mkGoalProblem (FromAF goalAF) p@(Problem (getGoalAF -> Nothing) trs dps) = do
    p' <- evProcessor p
    let orProblems = [(p' `withGoalAF` af) | af <- invariantEV_rhs p' (AF.init p `mappend` goalAF)]
    if null orProblems
      then failP (AFProc Nothing Nothing :: ProcInfo ()) p (toHtml "Could not find a sound AF")
      else msum (map return orProblems)

mkGoalProblem AllTerms p = return p

-- ------------------------------------------------------------------------
-- This is the AF processor described in our Dependency Pairs for Narrowing
-- ------------------------------------------------------------------------
{-# SPECIALIZE groundRhsP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE groundRhsP :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}

groundRhsP p@(Problem typ trs dps) | isAnyNarrowing typ =
    if null orProblems
      then failP (AFProc Nothing Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else msum orProblems
    where afs = findGroundAF (AF.init p) p =<< rules dps
          orProblems = [step (AFProc (Just af) Nothing) p $
                                AF.apply_rhs p af (mkProblem Rewriting trs dps)
                        | af <- afs]
          findGroundAF af0 p@(Problem typ trs dps) (_:->r)
            | isVar r   = mzero
            | otherwise = assertGroundDP `liftM` (toList(mkGround r) >>= invariantEV_rhs p)
            where -- mkGround :: Term f -> Set AF
              assertGroundDP af = assert (isGround $ AF.apply_rhs p af r) af
              mkGround t = cutWith (allInner p) af0 t varsp
                  where varsp = [TRS.note v | v <- vars' (annotateWithPos t), TRS.dropNote v `elem` vars' t]

groundRhsP p = return p

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

safeAFP p@(Problem (getGoalAF -> Just af) trs dps) = assert (isSoundAF af p) $
  step (AFProc (Just af) Nothing) p (AF.apply_rhs p af $ Problem Rewriting trs dps)

-- -----
-- Modes
-- -----

-- | Receives an initial goal (its modes) and a TRS and returns a Division
computeDivision,computeDivisionL :: (Identifier ~ id, TRSC f, T id :<: f, DPMark f id) => NarradarTRS id f -> Goal -> Division id
computeDivision  = computeDivision_ e
computeDivisionL = computeDivision_ (observe "eL" eL)

-- | Receives an initial goal (its modes) and a TRS and returns a Division
--computeDivision :: (Identifier ~ id, TRSC f, T id :<: f) => T id Mode -> TRS id f -> Division id
computeDivision_ e trs (T id_ tt) = Map.singleton id tt `meet` fixEq go div0
  where
    id = IdFunction id_
--    div0 :: Division Identifier
    div0 = Map.fromList ((id,tt) : [(id,replicate ar G)
                                    | id <- Set.toList(Set.delete id $ definedSymbols sig)
                                    , let ar = getArity sig id])
    sig  = getSignature trs
--    go :: Division Identifier -> Division Identifier
    go = observe "iteration" go'
    go' div = Map.mapWithKey (\f b ->
             lub (b : [ bv trs f (e f rule div) div r
                       | rule@(l:->r) <- rules trs])) div

e _g ( (open -> Just(T (f::Identifier) tt)) :-> _r) div =
        Map.fromListWith meet
               [ (i, m) | (vv,m) <- map vars' tt `zip` mydiv, v <- vv, let Just i = uniqueId v]
     where Just mydiv = Map.lookup f div

eL g rule@( (open -> Just(T (f::Identifier) tt)) :-> r) div
  | rootSymbol r == Just g = e g rule div
  | otherwise = lhs_vars `meet` rhs_vars
 where
  Just mydiv = Map.lookup f div
  lhs_vars = Map.fromListWith meet [ (i, m) | (vv,m) <- map vars' tt `zip` mydiv
                                            , v <- vv
                                            , let Just i = uniqueId v]
  rhs_vars = lub $ execWriter(evalStateT (mapM_ accumVars (properSubterms r)) Map.empty)
  accumVars t
   | rootSymbol t == Just g = do
     modify(meet (Map.fromList[(i,m)
                               | v <- vars' t, let Just i = uniqueId v
                               , let m = fromMaybe V (Map.lookup i lhs_vars)]))
     get >>= lift. tell.(:[])
     modify(meet (Map.fromList[(i,G) | v <- vars' t, let Just i = uniqueId v]))

   | otherwise = modify(join (Map.fromList[(i,G) | v <- vars' t, let Just i = uniqueId v]))


bv,bv' :: forall p id f . (Show id, Observable id, SignatureC p id, T id :<: f, TRSC f) =>
          p -> id -> DivEnv -> Division id -> Term f -> [Mode]
bv trs = observe "bv" (bv' trs)
bv' trs g rho div (open -> Just Var{}) = replicate (getArity (getSignature trs) g) G
bv' trs g rho div me@(open -> Just (T (f::id) tt))
--      | isConstructor trs me = bt
      | f /= g    = bt
      | otherwise = bt `join` (be <$> tt)
     where
       bt  = lub (bv trs g rho div <$> tt)
       be  = observe "be" be'
       be' (open -> Just (Var _ i)) | Just xrho <- Map.lookup i rho = xrho
       be' me@(open -> Just (T (f::id) tt))
                 -- note that this filters more than the algorithm in the paper
        | In me' <- AF.apply (divToAFfilterOutputs trs div) me = lub $ toList (be <$> me')


-- | Returns an AF which filters ground arguments from the TRS and also from the DPs.
divToAFfilterInputs p div = AF.init p `mappend`
                            AF.fromList (concat [ [(f, outputs ), (markDPSymbol f, outputs)]
                                                | (f,modes) <- Map.toList div
                                                , let outputs = [ i | (i,m) <- zip [1..] modes, m == V]])

-- | Filter variables.
divToAFfilterOutputs trs div = -- AF.init trs `mappend`
                               AF.fromList [ (f,  [ i | (i,m) <- zip [1..] modes, m == G])
                                        | (f,modes) <- Map.toList div]

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
