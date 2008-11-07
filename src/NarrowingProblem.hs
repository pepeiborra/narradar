{-# LANGUAGE PatternSignatures, PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}

module NarrowingProblem where

import Control.Exception
import Data.Foldable (Foldable)
import Data.List (sortBy)
import Data.Monoid
import Text.XHtml (toHtml, Html)
import Prelude as P

import qualified ArgumentFiltering as AF
import DPairs
import Problem
import Utils
import Types

mkNDPProblem trs = Problem Narrowing trs (tRS $ getNPairs trs)

afProcessor :: AnnotateWithPos f f => Problem f -> ProblemProgress Html f
afProcessor p@(Problem Narrowing trs dps) = if null orProblems
                                                  then Fail (AFProc mempty) p (toHtml "Could not find a grounding AF")
                                                  else Or   (AFProc mempty) p (sortByDefinedness orProblems)
    where afs = snub $ map (findGroundAF p) (rules dps)
          orProblems = [And (AFProc af) p [NotDone $ AF.applyAF af (Problem Rewriting trs dps)] | af <- afs]
          sortByDefinedness = sortBy (flip compare `on` (AF.countPositionsFiltered . (\(And (AFProc af) _ _)-> af)))


findGroundAF :: AnnotateWithPos f f => Problem f -> DP f -> AF.AF
findGroundAF p@(Problem _ trs@TRS{} dps) (_:->r) =
    ( assertNoExtraVars . assertGroundDP . invariantSignature . invariantExtraVars trs . invariantExtraVars dps) $ (mkGround r)
  where mkGround t
          | null pp = mempty
          | otherwise
          = AF.cutAll [ (root, [last p]) | p <- pp, let Just root = rootSymbol (t ! init p)] (AF.initAF p)
         where pp = varsPositions t
        invariantSignature af = AF.fromList [ (IdFunction f, pp) | (IdDP f, pp) <- AF.toList af] `mappend` af
        invariantExtraVars trs@TRS{} af
          | null extra = af
          | otherwise  = invariantExtraVars trs $
                           AF.cutAll [ (root,[last p]) | rule@(_:->r) <- rules $ AF.applyAF af trs
                                                       , let pp = varsPositions r
                                                       , v <- extraVars rule
                                                       , p <- pp
                                                       , r ! p == inject v
                                                       , let Just root = rootSymbol (r ! init p)]
                                  af
           where extra  = extraVars (AF.applyAF af trs)
        assertNoExtraVars af = assert (null $ extraVars $ AF.applyAF af trs) af
        assertGroundDP    af = assert (isGround $ AF.applyAF af r) af

varsPositions :: (AnnotateWithPos f f, Var :<: f, Foldable f) => Term f -> [Position]
varsPositions t = [ p | In(Note (p,t)) <- subterms (annotateWithPos t), Just Var{} <- [prj t] ]
