{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Narradar.ExtraVars where

import Control.Applicative
import Control.RMonad hiding (join)
import qualified Control.Monad as P
import Control.Monad.Fix
import Data.List (sortBy, inits, unfoldr, isPrefixOf, isSuffixOf, intersect)
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.XHtml (toHtml)
import Prelude hiding (Monad(..), (=<<), or, and, mapM)

import TRS
import Narradar.Utils(on)
import Lattice
import Narradar.ArgumentFiltering (AF, LabelledAF, AF_, Heuristic, bestHeu, typeHeu)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Types
import Narradar.Proof

#ifdef DEBUG
import Debug.Trace
#else
trace _ x = x
#endif

evProcessor p | not (isAnyNarrowingProblem p) = P.return p
evProcessor p@(Problem typ@(getProblemAF -> Just af) trs dps)
     | null extra      = P.return p
     | null orProblems = failP (EVProc mempty :: ProcInfo ()) p (toHtml "Could not find a EV-eliminating AF")
     | otherwise = P.msum (map P.return orProblems)
  where extra = extraVars p
        heu   = maybe (bestHeu p) typeHeu (getTyping typ)
        orProblems = [(p `withGoalAF` af') | af' <- invariantEV heu p af]

evProcessor p@(Problem typ trs dps) = evProcessor (p `withGoalAF` AF.init p)
evProcessor p = P.return p

{-# SPECIALIZE cutWith :: Heuristic Id BBasicId -> AF -> Term BBasicId -> [Position] -> Set.Set AF #-}
cutWith heu af t [] = return af
cutWith heu af t pp = foldM (\af' pos -> (heu af' t pos >>= \(f,p) ->
          trace ("term: " ++ show t ++ ", pos: " ++ show pos ++ ", symbol:" ++ show f ++ ", i: " ++ show p) $
          return$ AF.cut f p af'))
                            af pp
--cutWith heu af t pp = mconcat `liftM` (mapM (heu af t >=> \(f,p) -> return$ AF.cut f p af) pp)

{-# SPECIALIZE invariantEV :: Heuristic LId BBasicLId -> ProblemG LId BBasicLId -> LabelledAF -> [LabelledAF] #-}
{-# SPECIALIZE invariantEV :: Heuristic Id  BBasicId  -> Problem BBasicId -> AF -> [AF] #-}

invariantEV heu p@Problem{trs,dps} = sortByDefinedness AF.apply dps . selectBest . Set.toList
                                   . fix (\f -> subinvariantEV trs f >=> subinvariantEV dps f)
  where
--        subinvariantEV :: TRS Identifier f -> (AF -> Set AF) -> AF -> Set AF
        subinvariantEV trs f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (AF.apply af trs)
        cutEV af rule@(_:->r)
            | orig_poss <- note <$> extraVars (AF.apply af (annotateWithPos <$> rule))
            = cutWith heu af r orig_poss

invariantEV_rhs heu p@Problem{trs,dps} = sortByDefinedness (AF.apply_rhs p)  dps . selectBest . Set.toList
                                        . fix (\f -> subinvariantEV trs f >=> subinvariantEV dps f)
  where
--        subinvariantEV :: TRS Identifier f -> (AF -> Set AF) -> AF -> Set AF
        subinvariantEV trs f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (AF.apply_rhs p af trs)
        cutEV af rule@(_:->r)
            | orig_poss <- note <$> extraVars (AF.apply_rhs p af (annotateWithPos <$> rule))
            = cutWith heu af r orig_poss where
              cutWith heu af t [] = return af
              cutWith heu af t pp = foldM (\af' pos -> (heu af' t pos >>= \(f,p) ->
                         trace ("term: " ++ show t ++ ", pos: " ++ show pos ++ ", symbol:" ++ show f ++ ", i: " ++ show p ++ " rule: " ++ show rule) $
                         return$ AF.cut f p af'))
                                          af pp


sortByDefinedness :: (Ord id, Size trs) => (AF_ id -> trs -> trs) -> trs -> [AF_ id] -> [AF_ id]
sortByDefinedness apply dps = sortBy (flip compare `on` dpsSize)
    where dpsSize af = size (apply af dps)

selectBest = unfoldr findOne where
          findOne [] = Nothing
          findOne (m:xx)
              | any (\x -> Just True == lt m x) xx = findOne xx
              | otherwise = Just (m, filter (uncomparableTo m) xx)
              where uncomparableTo x y = isNothing (lt x y)

-- ----------
-- Soundness
-- ----------
isSoundAF     af trs = null (extraVars $ AF.apply     af trs)
--isSoundAF_rhs af trs = null (extraVars $ AF.apply_rhs af trs)

{-
-- ----------------------
-- Binding Time Analysis
-- ----------------------

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
-}