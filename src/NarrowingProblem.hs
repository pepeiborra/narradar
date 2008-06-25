{-# LANGUAGE PatternSignatures, PatternGuards #-}

module NarrowingProblem where

import Control.Arrow (first)
import Control.Monad
import Data.AlaCarte
import Data.Foldable (Foldable)
import Data.List ((\\), sortBy)
import Data.Monoid
import Text.XHtml (toHtml, Html)
import Prelude as P

import qualified ArgumentFiltering as AF
import DPairs
import Problem
import Utils
import Types

mkNDPProblem trs = Problem Narrowing trs (TRS $ getNPairs trs)

afProcessor :: AnnotateWithPos f f => Problem f -> ProblemProgress Html f
afProcessor p@(Problem Narrowing trs (TRS dps)) = if null orProblems
                                                  then Fail (AFProc mempty) p (toHtml "Could not find a grounding AF")
                                                  else Or   (AFProc mempty) p (sortByDefinedness orProblems)
    where afs = snub $ concatMap (findGroundAF p) dps
          orProblems = [And (AFProc af) p [NotDone $ AF.applyAF af (Problem Rewriting trs (TRS dps))] | af <- afs]
          sortByDefinedness = sortBy (flip compare `on` (AF.countPositionsFiltered . (\(And (AFProc af) p sp)-> af)))


findGroundAF :: AnnotateWithPos f f => Problem f -> DP f -> [AF.AF]
findGroundAF p@(Problem _ trs@(TRS rules) _) (l:->r) =
    snub . map (invariantExtraVars . invariantSignature) $ (mkGround r)

  where mkGround t
          | isGround t  = mempty
          | Just (T (f::Identifier) tt) <- match t
          = (map (AF.invert p . AF.fromList . concat) . sequence . inhabiteds . fmap2 AF.toList) [go f it | it <- zip [0..] tt]
          | isVar t     = error "mkGround: unreachable"
         where go f (i,t)
                   | isGround t   = mempty
                   | isVar t      = [AF.singleton f [i]]
                   | Just (T (f'::Identifier) tt) <- match t
                   = {- AF.singleton f [i] : -}
                     ((map AF.fromList . concat) . sequence . inhabiteds . fmap2 AF.toList $ [go f' it | it <- zip [0..] tt])
        invariantSignature af = AF.fromList [ (IdFunction f, pp) | (IdDP f, pp) <- AF.toList af] `mappend` af
        invariantExtraVars af
          | null extra = af
          | otherwise  = invariantExtraVars (foldr (uncurry AF.cut) af
                                            [ (root,[last p]) | rule <- rules
                                                              , Var n i   <- extraVars rule
                                                              , _ :-> rP  <- rulesP
                                                              , In(Note (p,t)) <- subterms rP
                                                              , let Just (Var n' i') = prj t
                                                              , n' == n && i' == i
                                                              , let In(Note (_,parent)) = rP ! init p
                                                              , let Just (T root _) = prj parent])
           where extra  = concatMap extraVars (AF.applyAF af rules)
                 rulesP = annotateWithPos <$$> rules