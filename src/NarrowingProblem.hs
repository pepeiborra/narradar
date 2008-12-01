{-# LANGUAGE PatternSignatures, PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}

module NarrowingProblem where

import Control.Applicative
import Control.Exception
import Control.Monad.Free
import Control.Monad.Fix (fix)
import Control.RMonad
import Data.Foldable (Foldable, foldMap)
import Data.List (sortBy, inits)
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import Text.XHtml (toHtml, Html)

import Prelude hiding (Monad(..), (=<<), mapM)
import qualified Prelude as P

import qualified ArgumentFiltering as AF
import DPairs
import Problem
import Utils
import Types
import TRS

mkNDPProblem trs = Problem Narrowing trs (tRS $ getNPairs trs)

afProcessor :: (Ord(Term f), IsVar f, AnnotateWithPos f f) => Problem f -> ProblemProgress Html f
afProcessor p@(Problem Narrowing trs dps@TRS{}) =
    if null orProblems
      then failP (AFProc Nothing) p (toHtml "Could not find a grounding AF")
      else orP (AFProc Nothing) p orProblems
    where afs = findGroundAF p =<< Set.fromList (rules dps)
          orProblems = [andP (AFProc $ Just af) p [P.return $ AF.applyAF af (Problem Rewriting trs dps)]
                            | af <- sortByDefinedness (Set.toList afs)]
          sortByDefinedness = sortBy (flip compare `on` dpsSize)
          dpsSize af = size (AF.applyAF af (rules dps))


findGroundAF :: forall f . (Ord(Term f), IsVar f, AnnotateWithPos f f) => Problem f -> DP f -> Set AF.AF
findGroundAF p@(Problem _ trs@TRS{} dps) (_:->r)
  | isVar r   = mzero
  | otherwise =
      (assertNoExtraVars . assertGroundDP) `liftM`
      (mkGround r >>= fix (\f -> invariantExtraVars trs f >=> invariantExtraVars dps f))
  where cutP af t [] = mzero
        cutP af t p  = Set.fromList
                       [ AF.cutAll [(root, [last sub_p])] af
                              | sub_p <- reverse (tail $ inits p)
                              , Just root <- [rootSymbol (t ! init sub_p)]]
        cutPP af t [] = return af
        cutPP af t pp = AF.concat `liftM` (mapM (cutP af t) pp)
        cutEV af rule@(_:->r)
            | extra <- extraVars (annotateWithPos <$> AF.applyAF af rule)
            = cutPP af r (map TRS.note extra)
        mkGround :: Term f -> Set AF.AF
        mkGround t = cutPP af0 t varsp
         where varsp   = varsPositions t
               af0     = AF.initAF p
--      invariantSignature af = AF.fromList [ (IdFunction f, pp) | (IdDP f, pp) <- AF.toList af] `AF.union` af -- I disabled this invariant since I don't think it is necessary. It is not in the theory (I cannot find it, at least)
--        invariantExtraVars :: TRS Identifier f -> AF.AF -> Set AF.AF
        invariantExtraVars trs@TRS{} f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (AF.applyAF af trs)
        assertNoExtraVars af = assert (null $ extraVars $ AF.applyAF af trs) $
                               assert (null $ extraVars $ AF.applyAF af dps) af
        assertGroundDP    af = assert (isGround $ AF.applyAF af r) af

varsPositions :: (AnnotateWithPos f f, Var :<: f, Foldable f) => Term f -> [Position]
varsPositions t = [ p | In(Note (p,t)) <- subterms (annotateWithPos t), Just Var{} <- [prj t] ]