{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
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
     MkProblem(..), mkGoalProblem,
     cutWith
             ) where

import Control.Applicative
import Control.Exception
import Control.Monad.Free hiding (note)
import Control.Monad.Fix (fix)
import Control.Monad.Writer(execWriter, execWriterT, MonadWriter(..), lift)
import Control.Monad.State (evalState, evalStateT, modify, MonadState(..))
import Control.RMonad hiding (join)
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (sortBy, inits, unfoldr, isPrefixOf, isSuffixOf, intersect)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Set (Set)
import Text.XHtml (toHtml, Html)

import Debug.Observe
import Debug.Trace
import Prelude hiding (Monad(..), (=<<), or, and, mapM)
import qualified Prelude as P
import qualified Control.Monad as P

import ArgumentFiltering (AF_,AF, LabelledAF, Heuristic, bestHeu, allInner)
import qualified ArgumentFiltering as AF
import DPairs
import Proof
import Utils
import Types
import TRS
import Lattice

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
mkGoalProblem (FromAF goalAF) p@(Problem typ trs dps) =
    if null orProblems
      then failP (AFProc Nothing Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else P.msum (map P.return orProblems)
    where afs        = invariantEV p (AF.init p `mappend` goalAF)
          bestAfs    = (sortByDefinedness dps . selectBest . Set.toList) afs
          orProblems = [(p `withGoalAF` af)
                            | af <- bestAfs]

mkGoalProblem AllTerms p = P.return p

{-
afProcessor p@(Problem (RewritingAF af) trs dps@TRS{}) =
    let Problem _ trs' dps' = AF.apply af p in return $ Problem Rewriting trs' dps'
-}
--afProcessor :: (Bottom :<: f, Show id) => ProblemG id f -> ProblemProofG id Html f
{-# SPECIALIZE afProcessor :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE afProcessor :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
afProcessor p@(Problem (getGoalAF -> Just af) trs dps) =
  step (AFProc (Just af) Nothing) p (AF.apply af $ Problem Rewriting trs dps)

afProcessor p@(Problem typ trs dps) | isAnyNarrowing typ =
    if null orProblems
      then failP (AFProc Nothing Nothing :: ProcInfo ()) p (toHtml "Could not find a grounding AF")
      else P.msum orProblems
    where afs = findGroundAF (AF.init p) p =<< Set.fromList (rules dps)
          orProblems = [step (AFProc (Just af) Nothing) p $
                                AF.apply af (mkProblem Rewriting trs dps)
                            | af <- (sortByDefinedness . selectBest . Set.toList) afs]
          sortByDefinedness = sortBy (flip compare `on` dpsSize)
          selectBest = unfoldr findOne
          findOne [] = Nothing
          findOne (m:xx)
              | any (\x -> Just True == lt m x) xx = findOne xx
              | otherwise = Just (m, filter (uncomparableTo m) xx)
              where uncomparableTo x y = isNothing (lt x y)
          dpsSize af = size (AF.apply af dps)


afProcessor p = P.return p

sortByDefinedness :: (AF.ApplyAF trs id, Ord id, Size trs) => trs -> [AF_ id] -> [AF_ id]
sortByDefinedness dps = sortBy (flip compare `on` dpsSize) where dpsSize af = size (AF.apply af dps)
selectBest = unfoldr findOne where
          findOne [] = Nothing
          findOne (m:xx)
              | any (\x -> Just True == lt m x) xx = findOne xx
              | otherwise = Just (m, filter (uncomparableTo m) xx)
              where uncomparableTo x y = isNothing (lt x y)

{-# SPECIALIZE findGroundAF :: AF -> Problem BBasicId -> DP BBasicId -> Set AF #-}
{-# SPECIALIZE findGroundAF :: AF_ LId -> ProblemG LId BBasicLId -> DP BBasicLId -> Set LabelledAF #-}
--findGroundAF :: forall f id. (Bottom :<: f) => AF -> ProblemG id f -> DP f -> Set (AF_ id)
findGroundAF af0 p@(Problem typ trs dps) (_:->r)
  | isVar r   = mzero
  | otherwise = assertGroundDP `liftM` (mkGround r >>= invariantEV p)
  where -- mkGround :: Term f -> Set AF
        mkGround t = cutWith (allInner p) af0 t varsp
         where varsp   = [TRS.note v | v <- vars' (annotateWithPos t), TRS.dropNote v `elem` vars' t]
        assertNoExtraVars af = assert (null $ extraVars $ AF.apply af trs) $
                               assert (null $ extraVars $ AF.apply af dps) af
        assertGroundDP    af = assert (isGround $ AF.apply af r) af
--      invariantSignature af = AF.fromList [ (IdFunction f, pp) | (IdDP f, pp) <- AF.toList af] `AF.union` af -- I disabled this invariant since I don't think it is necessary. It is not in the theory (I cannot find it, at least)


{-# SPECIALIZE cutWith :: Heuristic Id BBasicId -> AF -> Term BBasicId -> [Position] -> Set.Set AF #-}
cutWith heu af t [] = return af
--cutWith heu af t pp = foldM (\af' p -> (heu af' t p >>= \(f,p) -> return$ AF.cut f p af')) af pp
cutWith heu af t pp = mconcat `liftM` (mapM (heu af t >=> \(f,p) -> return$ AF.cut f p af) pp)

--invariantEV :: AF -> Set AF
{-# SPECIALIZE invariantEV :: ProblemG LId BBasicLId -> LabelledAF -> Set LabelledAF #-}
{-# SPECIALIZE invariantEV :: Problem BBasicId -> AF -> Set AF #-}
invariantEV p@Problem{..} = fix (\f -> subinvariantEV trs f >=> subinvariantEV dps f)
  where
--        subinvariantEV :: TRS Identifier f -> (AF -> Set AF) -> AF -> Set AF
        subinvariantEV trs f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (AF.apply af trs)
        cutEV af rule@(_:->r)
            | orig_poss <- note <$> extraVars (AF.applyToRule (getSignature p) af (annotateWithPos <$> rule))
            = cutWith (bestHeu p) af r orig_poss

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
  rhs_vars = lub $ execWriter(evalStateT (P.mapM_ accumVars (properSubterms r)) Map.empty)
  accumVars t
   | rootSymbol t == Just g =
    modify(meet (Map.fromList[(i,m)
                             | v <- vars' t, let Just i = uniqueId v
                             , let m = fromMaybe V (Map.lookup i lhs_vars)])) P.>>
    get P.>>= lift. tell.(:[]) P.>>
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

-- ----------
-- Labelling
-- ----------
type InverseAF = AF


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
