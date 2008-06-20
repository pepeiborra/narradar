module NarrowingProblem where

import Control.Arrow (first)
import Control.Monad
import Data.AlaCarte
import Data.Foldable (Foldable)
import Data.List ((\\))
import Data.Monoid
import Text.XHtml (toHtml)
import Prelude as P

import qualified ArgumentFiltering as AF
import DPairs
import Problem
import Utils
import Types

mkNDPProblem trs = Problem Narrowing trs (getNPairs trs)




graphProcessor problem@(Problem Narrowing trs dps) =
    And DependencyGraph problem [NotDone $ Problem Narrowing trs  (map (dps !!) ciclo) | ciclo <- cc]
    where cc = cycles $ getEDG trs dps





afProcessor problem@(Problem Narrowing trs dps) = if null orProblems
                                                  then Fail NarrowingAF problem (toHtml "Could not find a grounding AF")
                                                  else Or NarrowingAF problem orProblems
    where afs = snub $ concatMap (findGroundAF trs) dps
          orProblems = [And (AFProc af) problem [NotDone $ AF.applyAF af (Problem Rewriting trs dps)] | af <- afs]


findGroundAF :: (Var :<: f, Foldable f) => TRS sig f -> DP f -> [AF.AF]
findGroundAF rules (l:->r) =
    snub . filter (not.extraVars) . map invariant $ (mkGround r)

  where mkGround :: Term f -> [AF.AF]
        mkGround t
          | isGround t  = mempty
          | Just (T f tt) <- match t
          = undefined -- (map (AF.invert rules . AF.fromList) . sequence . inhabiteds . map AF.toList) [go f it | it <- zip [0..] tt]
          | isVar t     = error "mkGround: unreachable"
         where go f (i,t)
                   | isGround t   = mempty
                   | isVar t      = [AF.singleton f [i]]
                   | Just (T f' tt) <- match t
                   = AF.singleton f [i] : ((map AF.fromList . concat) . sequence . inhabiteds . fmap2 AF.toList $ [go f' it | it <- zip [0..] tt])
        invariant af = AF.fromList [ (f, pp) | (IdDP' f, pp) <- AF.toList af] `mappend` af
        extraVars af = hasExtraVars (AF.applyAF af rules)
