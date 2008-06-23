{-# LANGUAGE PatternGuards, OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module Problem where

import Control.Applicative
import Control.Monad (join)
import Data.AlaCarte
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable as T
import Data.HashTable (hashString)
import Data.Maybe
import qualified Data.Map as Map
import Data.Traversable as T
import Terms
import Text.PrettyPrint
import Text.Printf
import qualified Text.XHtml as H
import Text.XHtml (HTML(..), Html(..), (<<), (+++), (!), p, br, noHtml, theclass, hotlink, thediv
                  ,identifier,table,td)
import Text.XHtml.Table
import System.IO.Unsafe
import Unsafe.Coerce

import Types hiding (Ppr(..),ppr, (!))
import qualified Types as TRS
import Utils
import qualified ArgumentFiltering as AF

import Prelude as P hiding (log, mapM, foldr, concatMap)

data Problem_ a = Problem  ProblemType a a
     deriving (Eq,Show)

type Problem f = Problem_ (TRS f)

data ProblemType = Rewriting | Narrowing
     deriving (Eq, Show)

data Progress_ f s a =   NotDone    a
                       | And        {procInfo::ProcInfo, problem::Problem f, subProblems::[Progress_ f s a]}
                       | Or         {procInfo::ProcInfo, problem::Problem f, subProblems::[Progress_ f s a]}
                       | Success    {procInfo::ProcInfo, problem::Problem f, res::s}
                       | Fail       {procInfo::ProcInfo, problem::Problem f, res::s}
                       | Empty
     deriving (Show)

type ProblemProgress s f = Progress_ f s (Problem f)

data ProcInfo = AFProc AF.AF
              | DependencyGraph
              | Polynomial
              | External ExternalProc
     deriving (Eq, Show)

data ExternalProc = MuTerm | Aprove | Other String
     deriving (Eq, Show)

instance Foldable Problem_ where foldMap = foldMapDefault
$(derive makeFunctor     ''Problem_)
$(derive makeTraversable ''Problem_)

instance Foldable (Progress_ f s) where foldMap = foldMapDefault
$(derive makeFunctor     ''Progress_)
$(derive makeTraversable ''Progress_)

instance Monad (Progress_ f s) where
    return   = NotDone
    xs >>= f = join (fmap f xs)
      where join (NotDone p)    = p
            join (And pi pr pp) = And pi pr (map join pp)
            join (Or  pi pr pp) = Or  pi pr (map join pp)
            join p              = unsafeCoerce p

success NotDone{} = False
success Success{} = True
success Fail{}    = False
success (And _ _ ll)  = P.all success ll
success (Or  _ _ ll)  = P.any success ll
success Empty     = True

solveProblem :: (Problem a -> ProblemProgress s a) -> ProblemProgress s a -> ProblemProgress s a
solveProblem = (=<<)

class Monad m => SolveProblemM m where
  solveProblemM :: (Problem a -> m (ProblemProgress s a)) -> ProblemProgress s a -> m (ProblemProgress s a)
  solveProblemM = concatMapM

instance SolveProblemM IO


simplify p@(Or pi pb aa) | success p = listToMaybe [p | p <- aa, success p]
simplify p = Nothing

logLegacy proc prob Nothing = Fail proc prob "Failed"
logLegacy proc prob (Just msg) = Success proc prob msg

pprSkelt Fail{}    = text "failure"
pprSkelt Success{} = text "success"
pprSkelt NotDone{} = text "not done"
pprSkelt Empty     = text "empty"
pprSkelt (And _ _ pp) = parens $ cat $ punctuate (text " & ") $ map pprSkelt pp
pprSkelt (Or _ _ pp)  = parens $ cat $ punctuate (text " | ") $ map pprSkelt pp

pprTPDB :: TRS.Ppr f => Problem f -> String
pprTPDB (Problem _ (TRS rules) (TRS dps)) =
  unlines [ printf "(VARS %s)" (unwords $ map (show . inject) $ snub $ P.concat (foldMap vars <$> rules))
          , printf "(PAIRS\n %s)" (unlines (map (show . unmarkDPRule) dps))
          , printf "(RULES\n %s)" (unlines (map show rules))]

-------------------
-- Ppr
-------------------

class Ppr a where ppr :: a -> Doc

instance (Functor f, Foldable f, Ppr x) => Ppr (f x) where ppr = brackets . vcat . punctuate comma . toList . fmap ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance Show (Term a) => Ppr (Rule a) where ppr = text . show
instance TRS.Ppr f => Ppr (TRS f) where ppr (TRS trs) = ppr trs

instance Ppr ProblemType where
    ppr Narrowing = text "NDP"
    ppr Rewriting = text "DP"

instance TRS.Ppr a => Ppr (Problem a) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps


instance TRS.Ppr a => Ppr (ProblemProgress String a) where
    ppr (NotDone prob) = ppr prob $$
                         text ("RESULT: Not solved yet")
    ppr (Success proc prob res) = ppr prob $$
                                  text "PROCESSOR: " <> text (show proc) $$
                                  text ("RESULT: Problem solved succesfully") $$
                                  text ("Output: ") <>  (vcat . map text . lines) res
    ppr (Fail proc prob res) = ppr prob $$
                               text "PROCESSOR: " <> (text.show) proc  $$
                               text ("RESULT: Problem could not be solved.") $$
                               text ("Output: ") <> (vcat . map text . lines) res
    ppr p@(Or proc prob sub) | Just res <- simplify p = ppr res
                  | otherwise =
                     ppr prob $$
                     text "PROCESSOR: " <> (text.show) proc $$
                     text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
                     nest 8 (vcat $ punctuate (text "\n") (map ppr sub))
    ppr (And proc prob sub)
        | length sub > 1=
                     ppr prob $$
                     text "PROCESSOR: " <> (text.show) proc $$
                     text ("Problem was divided to " ++ show (length sub) ++ " subproblems.") $$
                     nest 8 (vcat $ punctuate (text "\n") (map ppr sub))
        | otherwise =
                     ppr prob $$
                     text "PROCESSOR: " <> (text.show) proc $$
                     nest 8 (vcat $ punctuate (text "\n") (map ppr sub))
--------------
-- HTML
-------------

instance HTML a => HTMLTABLE a where cell = cell . toHtml

instance HTML AF.AF where
    toHtml (AF.AF af) = toHtml $ show $ Map.toList af

instance HTML Doc where toHtml = toHtml . show

instance HTML ProcInfo where
    toHtml (AFProc af)     = "PROCESSOR: " +++ "Argument Filtering " +++ af
    toHtml DependencyGraph = "PROCESSOR: " +++ "Dependency Graph (cycle)"
    toHtml Polynomial      = "PROCESSOR: " +++ "Polynomial Interpretation"
    toHtml (External e)    = "PROCESSOR: " +++ "External - " +++ show e

instance TRS.Ppr f => HTML (Problem f) where
    toHtml (Problem typ (TRS rr) (TRS [])) =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules"</> aboves rr </>
                 "Dependency Pairs: none")
    toHtml (Problem typ (TRS rr) (TRS dps)) =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules" </>
                 aboves rr </>
            H.td ! [H.theclass "DPS" ] << "Dependency Pairs" </>
                 aboves dps)

instance TRS.Ppr f => HTML (ProblemProgress Html f) where
    toHtml (NotDone prob) = p << prob
    toHtml (Success proc prob res) =
        p
        << prob +++ br +++
           proc +++ br +++
           divyes +++ thickbox res << spani "seeproof" << "(see proof)"

    toHtml (Fail proc prob res) =
        p
        << prob +++ br +++
           proc +++ br +++
           divmaybe +++ thickbox res << spani "seeproof" << "(see failure)"

    toHtml pr@(Or proc prob sub)
        | Just res <- simplify pr = toHtml res
        | otherwise = p
                      << prob +++ br +++
                         proc +++ br +++
                          "Problem was translated to " +++ show(length sub) +++ " equivalent alternatives" +++ br +++
                          H.unordList sub
    toHtml (And proc prob sub) =
        p
        << prob +++ br +++
           proc +++ br +++
--           "Problem was divided in " +++ show(length sub) +++ " subproblems" +++ br +++
           H.unordList sub

instance (T Identifier :<: f, TRS.Ppr f) =>  HTMLTABLE (Rule f) where
    cell r | (lhs :-> rhs ) <- unmarkDPRule r =
                                td ! [theclass "lhs"]   << show lhs <->
                                td ! [theclass "arrow"] << (" " +++ H.primHtmlChar "#x2192" +++ " ") <->
                                td ! [theclass "rhs"]   << show rhs

typClass Narrowing = theclass "NDP"
typClass Rewriting = theclass "DP"

divi ident = H.thediv ! [H.theclass ident]
spani ident = H.thespan ! [H.theclass ident]
divresult = spani "result" << "RESULT: "
divyes    = divresult +++ spani "yes" << "YES. "
divmaybe  = divresult +++ spani "maybe" << "Fail. "
thickbox thing c | label <- hashHtml thing =
         thediv ! [H.identifier ("tb"++label), H.thestyle "display:none"] << p << thing +++
         H.hotlink ("#TB_inline?height=600&width=600&inlineId=tb" ++ label) ! [theclass "thickbox"] << c

hashHtml = show . abs . hashString . H.renderHtml