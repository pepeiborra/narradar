{-# LANGUAGE PatternSignatures, PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}

module NarrowingProblem where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Free
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

import TRS.Utils (fixM_Eq)

mkNDPProblem trs = Problem Narrowing trs (tRS $ getNPairs trs)

afProcessor :: (IsVar f, AnnotateWithPos f f) => Problem f -> ProblemProgress Html f
afProcessor p@(Problem Narrowing trs dps) =
    if null orProblems
      then failP (AFProc AF.empty) p (toHtml "Could not find a grounding AF")
      else orP   (AFProc AF.empty) p (Impure <$> sortByDefinedness orProblems)
    where afs = snub $ map (findGroundAF p) (rules dps)
          orProblems = [And (AFProc af) p [return $ AF.applyAF af (Problem Rewriting trs dps)] | Just af <- afs]
          sortByDefinedness = sortBy (flip compare `on` (AF.countPositionsFiltered . (\(And (AFProc af) _ _)-> af)))


findGroundAF :: (IsVar f, AnnotateWithPos f f) => Problem f -> DP f -> Maybe AF.AF
findGroundAF p@(Problem _ trs@TRS{} dps) (_:->r)
  | isVar r   = Nothing
  | otherwise =
      assertNoExtraVars . assertGroundDP <$> mkGround r >>= fixM_Eq (invariantExtraVars trs >=> invariantExtraVars dps)
  where mkGround t
          | isVar t = fail "mkGround: cannot make a variable ground"
          | null pp || any null pp = return AF.empty
          | otherwise
          = return $ AF.cutAll [ (root, [last p]) | p <- pp, let Just root = rootSymbol (t ! init p)] (AF.initAF p)
         where pp = varsPositions t
        invariantSignature af = AF.fromList [ (IdFunction f, pp) | (IdDP f, pp) <- AF.toList af] `AF.union` af -- I disabled this invariant since I don't think it is necessary. It is not in the theory (I cannot find it, at least)
        invariantExtraVars trs@TRS{} af
          | null extra = return af
          | otherwise  = invariantExtraVars trs =<<
                           ((`AF.cutAll` af) . concat) <$>(
                             forM (rules $ AF.applyAF af trs) $ \ rule@(_:->r) -> do
                                           let extra = extraVars rule
                                           guard (not (isVar r && not(null extra)))
                                           return [ (root,[last p])
                                                       | v <- extra
                                                       , p <- varsPositions r
                                                       , r ! p == inject v
                                                       , let Just root = rootSymbol (r ! init p)])

           where extra  = extraVars (AF.applyAF af trs)
        assertNoExtraVars af = assert (null $ extraVars $ AF.applyAF af trs) af
        assertGroundDP    af = assert (isGround $ AF.applyAF af r) af

varsPositions :: (AnnotateWithPos f f, Var :<: f, Foldable f) => Term f -> [Position]
varsPositions t = [ p | In(Note (p,t)) <- subterms (annotateWithPos t), Just Var{} <- [prj t] ]
