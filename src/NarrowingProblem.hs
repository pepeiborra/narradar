{-# LANGUAGE PatternSignatures, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module NarrowingProblem where

import Control.Applicative
import Control.Exception
import Control.Monad.Free
import Control.Monad.Fix (fix)
import Control.Monad.Writer(execWriter, execWriterT, MonadWriter(..), lift)
import Control.Monad.State (evalState, evalStateT, modify, MonadState(..))
import Control.RMonad hiding (join)
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (sortBy, inits, unfoldr, isPrefixOf,intersect)
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

import qualified ArgumentFiltering as AF
import DPairs
import Proof
import Utils
import Types
import TRS
import Lattice

mkNDPProblem Nothing trs = P.return $ Problem Narrowing trs (tRS' $ getNPairs trs)
mkNDPProblem  (Just goal) trs = mkGoalProblem goal $ Problem Narrowing trs (tRS' $ getNPairs trs)
mkBNDPProblem Nothing     trs = P.return $ Problem BNarrowing trs (tRS' $ getPairs trs)
mkBNDPProblem (Just goal) trs = mkGoalProblem goal $ Problem BNarrowing  trs (tRS' $ getPairs trs)
mkLBNDPProblem(Just goal) trs = mkGoalProblem goal $ Problem LBNarrowing trs (tRS' $ getPairs trs)

mkGoalProblem :: Goal -> Problem f -> ProblemProof Html f
mkGoalProblem (T goal modes) p@(Problem typ trs dps@TRS{}) =
    if null orProblems
      then failP (AFProc Nothing Nothing) p (toHtml "Could not find a grounding AF")
      else P.msum (map P.return orProblems)
    where afs  = do dp <- Set.fromList (rules dps)
                    guard (rootSymbol (lhs dp) == Just (IdDP goal))
                    invariantEV p goalAF
          goalAF = AF.init p `mappend`
                   let pp = [ i | (i,m) <- zip [1..] modes, m == G]
                   in AF.fromList [(IdFunction goal, pp), (IdDP goal, pp)]
          orProblems = [(p `withGoalAF` af)
                            | af <- (sortByDefinedness dps . selectBest . Set.toList) afs]
{-
afProcessor p@(Problem (RewritingAF af) trs dps@TRS{}) =
    let Problem _ trs' dps' = AF.apply af p in return $ Problem Rewriting trs' dps'
-}
afProcessor p@(Problem (getGoalAF -> Just af) trs dps@TRS{}) =
  step (AFProc (Just af) Nothing) p (AF.apply af $ Problem Rewriting trs dps)

afProcessor p@(Problem typ trs dps@TRS{}) | isAnyNarrowing typ =
    if null orProblems
      then failP (AFProc Nothing Nothing) p (toHtml "Could not find a grounding AF")
      else P.msum orProblems
    where afs = findGroundAF (AF.init p) p =<< Set.fromList (rules dps)
          orProblems = [step (AFProc (Just af) Nothing) p $
                                AF.apply af (Problem Rewriting trs dps)
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

sortByDefinedness dps = sortBy (flip compare `on` dpsSize) where dpsSize af = size (AF.apply af dps)
selectBest = unfoldr findOne where
          findOne [] = Nothing
          findOne (m:xx)
              | any (\x -> Just True == lt m x) xx = findOne xx
              | otherwise = Just (m, filter (uncomparableTo m) xx)
              where uncomparableTo x y = isNothing (lt x y)

findGroundAF :: forall f . (Ord(Term f), IsVar f, AnnotateWithPos f f) => AF.AF -> Problem f -> DP f -> Set AF.AF
findGroundAF af0 p@(Problem typ trs@TRS{} dps) (_:->r)
  | isVar r   = mzero
  | otherwise = assertGroundDP `liftM` (mkGround r >>= invariantEV p)
  where mkGround :: Term f -> Set AF.AF
        mkGround t = cutWith (allPos p) af0 t varsp
         where varsp   = [TRS.note v | v <- vars' (annotateWithPos t), TRS.dropNote v `elem` vars' t]
        assertNoExtraVars af = assert (null $ extraVars $ AF.apply af trs) $
                               assert (null $ extraVars $ AF.apply af dps) af
        assertGroundDP    af = assert (isGround $ AF.apply af r) af
--      invariantSignature af = AF.fromList [ (IdFunction f, pp) | (IdDP f, pp) <- AF.toList af] `AF.union` af -- I disabled this invariant since I don't think it is necessary. It is not in the theory (I cannot find it, at least)

cutWith heu af t [] = return af
cutWith heu af t pp = mconcat `liftM` (mapM (heu af t) pp)

--invariantEV :: AF.AF -> Set AF.AF
invariantEV p@Problem{..} = fix (\f -> subinvariantEV trs f >=> subinvariantEV dps f)
  where
        subinvariantEV :: TRS Identifier f -> (AF.AF -> Set AF.AF) -> AF.AF -> Set AF.AF
        subinvariantEV trs@TRS{} f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (AF.apply af trs)
        cutEV af rule@(_:->r)
            | orig_poss <- [TRS.note v | v <- vars' (annotateWithPos r), TRS.dropNote v `elem` extra]
            = cutWith (bestHeu p) af r orig_poss
             where extra = extraVars (AF.applyToRule (getSignature p) af rule)

varsPositions :: (AnnotateWithPos f f, Var :<: f, Foldable f) => Term f -> [Position]
varsPositions t = [ p | In(Note (p,t)) <- subterms (annotateWithPos t), Just Var{} <- [prj t] ]

-- -----------
-- Heuristics
-- -----------
bestHeu = (noConstructors `and` noUs) `or` allPos

type Heuristic f = Problem f -> AF.AF -> Term f -> Position -> Set (Identifier, Int)
innermost _ _ _ [] = mempty
innermost p af t pos | Just root <- rootSymbol (t ! init pos) = Set.singleton (root, last pos)
outermost _ _ _ [] = mempty
outermost p af t pos | Just root <- rootSymbol t = Set.singleton (root, head pos)

noConstructors _ _ _  []  = mempty
noConstructors p af t pos = Set.fromList
                       [ AF.cutAll [(root, last sub_p)] af
                              | sub_p <- reverse (tail $ inits pos)
                              , Just root <- [rootSymbol (t ! init sub_p)],
                              not (root `Set.member` constructorSymbols (getSignature p))]
noUs _ _ _  []  = mempty
noUs p af t pos = Set.fromList
                       [ AF.cutAll [(root, last sub_p)] af
                              | sub_p <- reverse (tail $ inits pos)
                              , Just root <- [rootSymbol (t ! init sub_p)],
                              not (isU root)]
  where isU(IdDP ('u':'_':_)) = True; isU _ = False


allPos _ _ _ []   = mempty
allPos p af t pos = Set.fromList
                       [ AF.cutAll [(root, last sub_p)] af
                              | sub_p <- reverse (tail $ inits pos)
                              , Just root <- [rootSymbol (t ! init sub_p)]]

and h1 h2 p af t pos = let
    afs1 = h1 p af t pos
    afs2 = h2 p af t pos
    in afs1 `Set.intersection` afs2

or h1 h2 p af t pos = case h1 p af t pos of
                        afs | Set.null afs -> h2 p af t pos
                            | otherwise    -> afs
-- -----
-- Modes
-- -----

-- | Receives an initial goal (its modes) and a TRS and returns a Division
computeDivision,computeDivisionL :: (Identifier ~ id, TRSC f, T id :<: f) => TRS id f -> Goal -> Division id
computeDivision  = computeDivision_ e
computeDivisionL = computeDivision_ (observe "eL" eL)

-- | Receives an initial goal (its modes) and a TRS and returns a Division
--computeDivision :: (Identifier ~ id, TRSC f, T id :<: f) => T id Mode -> TRS id f -> Division id
computeDivision_ e trs@TRS{} (T id_ tt) = Map.singleton id tt `meet` fixEq go div0
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


bv,bv' :: (TRSC f, T Identifier :<: f) => TRS Identifier f -> Identifier -> DivEnv -> Division Identifier -> Term f -> [Mode]
bv trs = observe "bv" (bv' trs)
bv' trs g rho div (open -> Just Var{}) = replicate (getArity (getSignature trs) g) G
bv' trs g rho div me@(open -> Just (T f tt))
--      | isConstructor trs me = bt
      | f /= g    = bt
      | otherwise = bt `join` (be <$> tt)
     where
       bt  = lub (bv trs g rho div <$> tt)
       be  = observe "be" be'
       be' (open -> Just (Var _ i)) | Just xrho <- Map.lookup i rho = xrho
       be' me@(open -> Just (T (f::Identifier) tt))
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
