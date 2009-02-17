{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Output where

import Control.Applicative
import Control.Monad.Free
import Data.HashTable (hashString)
import Data.Foldable
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint
import Text.Printf
import Text.Show
import qualified Text.XHtml as H
import Text.XHtml (HTML(..), Html(..), (<<), (+++), (!), p, br, noHtml, theclass, hotlink, thediv
                  ,identifier,table,td)
import Text.XHtml.Table

import qualified ArgumentFiltering as AF
import Proof
import Types hiding (Ppr(..),ppr, (!))
import qualified Types as TRS
import qualified TRS
import Utils (snub, foldMap3)

import qualified Language.Prolog.Syntax as Prolog

import Prelude hiding (concat)
-- ----
-- TPDB
-- ----

pprTPDB :: forall f id. (Show id, Bottom :<: f, DPSymbol id) => ProblemG id f -> String
pprTPDB p@(Problem _ trs dps@TRS{} ) =
  unlines [ printf "(VAR %s)" (unwords $ map (show . pprTerm) $ snub $ foldMap3 vars' ( rules <$> p))
          , printf "(PAIRS\n %s)" (unlines (map (show.pprRule) (rules dps)))
          , printf "(RULES\n %s)" (unlines (map (show.pprRule) (rules trs)))]

  where pprRule (a:->b) = pprTerm a <+> text "->" <+> pprTerm b
        pprTerm = foldTerm f
        f (prj -> Just (Var i n))               = ppr (var n :: Term f)
        f (prj -> Just (T (id::id) [])) = text (show id)
        f (prj -> Just (T (id::id) tt)) =
            text (show id) <> parens (hcat$ punctuate comma tt)
        f (prj -> Just Bottom) =  -- TODO Cache the obtained representation on first call
            text $ fromJust $ find (not . flip Set.member (allSymbols$getSignature p) . functionSymbol)
                                   ("_|_":["_|_"++show i | i <- [0..]])

-------------------
-- Ppr
-------------------

class Ppr a where ppr :: a -> Doc

instance (Functor f, Foldable f, Ppr x) => Ppr (f x) where ppr = brackets . vcat . punctuate comma . toList . fmap ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance Show (Term a)  => Ppr (Rule a) where ppr = text . show
instance TRS.Ppr f      => Ppr (NarradarTRS id f) where ppr trs@TRS{} = ppr $ rules trs
instance Ppr Int where ppr = int

instance TRS.Ppr f => Ppr (Term f) where ppr = TRS.ppr
instance Ppr (ProblemType id) where
    ppr Prolog                    = text "Prolog"
    ppr typ | isFullNarrowing typ = text "NDP"
    ppr typ | isBNarrowing typ    = text "BNDP"
    ppr Rewriting                 = text "DP"

instance TRS.Ppr f => Ppr (ProblemG id f) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps

instance Ppr SomeProblem where
  ppr (SomeProblem p@(Problem typ TRS{} _)) = ppr p
  ppr (SomePrologProblem gg cc) = ppr (mkPrologProblem gg cc :: Problem BasicId)

instance Ppr SomeInfo where ppr (SomeInfo p) = ppr p

instance TRS.Ppr a => Ppr (ProblemProof String a) where
    ppr = foldFree leaf f . simplify where
      leaf prob = ppr prob $$ text ("RESULT: Not solved yet")
      f MZero = text "don't know"
      f Success{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        text ("RESULT: Problem solved succesfully") $$
        text ("Output: ") <>  (vcat . map text . lines) res
      f Fail{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Problem could not be solved.") $$
        text ("Output: ") <> (vcat . map text . lines) res
      f p@(Or proc prob sub) =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
        nest 8 (vcat $ punctuate (text "\n") sub)
      f (And proc prob sub)
       | length sub > 1 =
          ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was divided to " ++ show (length sub) ++ " subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") sub)
       | otherwise =
          ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        nest 8 (vcat $ punctuate (text "\n") sub)
      f (Step{..}) =
          ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        nest 8 subProblem

instance Show id => Ppr (ProcInfo id) where ppr = text . show
--------------
-- HTML
-------------

instance HTML a => HTMLTABLE a where cell = cell . toHtml

instance Show id => HTML (AF.AF_ id) where
    toHtml (AF.AF af) = H.unordList [ pi +++ "(" +++ show k +++ ") = " +++ show ii  | (k,ii) <- Map.toList af]
        where pi = H.primHtmlChar "pi"

instance HTML Doc where toHtml = toHtml . show

instance Show id => HTML (ProcInfo id) where
    toHtml (AFProc af Nothing)    = "PROCESSOR: " +++ "Argument Filtering " +++ af
    toHtml (AFProc af (Just div)) = "PROCESSOR: " +++ "Argument Filtering " +++ af +++ showParen True (shows div) ""
    toHtml (EVProc af)            = "PROCESSOR: " +++ "Eliminate Extra Vars " +++ af
    toHtml DependencyGraph{} = "PROCESSOR: " +++ "Dependency Graph (cycle)"
    toHtml Polynomial      = "PROCESSOR: " +++ "Polynomial Interpretation"
    toHtml NarrowingP      = "PROCESSOR: " +++ "Narrowing Processor"
    toHtml (External e)    = "PROCESSOR: " +++ "External - " +++ show e
    toHtml InstantiationP  = "PROCESSOR: " +++ "Graph Transformation via Instantiation"
    toHtml FInstantiationP = "PROCESSOR: " +++ "Graph Transformation via Forward Instantiation"
    toHtml NarrowingP      = "PROCESSOR: " +++ "Graph Transformation via Narrowing"
    toHtml Trivial         = "PROCESSOR: " +++ "Trivial non-termination"
    toHtml p               = "PROCESSOR: " +++ show p

--instance HTML Prolog.Program where toHtml = show . Prolog.ppr

instance TRS.Ppr f => HTML (ProblemG id f) where
    toHtml (Problem typ trs dps@TRS{}) | null $ rules dps =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules"</> aboves (rules trs) </>
                 "Dependency Pairs: none")
    toHtml PrologProblem{..} =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Clauses" </> aboves program)
    toHtml (Problem typ trs dps@TRS{}) =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules" </>
                 aboves (rules trs) </>
            H.td ! [H.theclass "DPS" ] << "Dependency Pairs" </>
                 aboves (rules dps))

instance HTML SomeProblem where
    toHtml (SomeProblem p@Problem{}) = toHtml p
    toHtml (SomePrologProblem gg cc) = toHtml (mkPrologProblem gg cc :: Problem BasicId)

instance HTML SomeInfo where toHtml (SomeInfo pi) = toHtml pi

instance TRS.Ppr f => HTML (ProblemProofG id Html f) where
   toHtml = foldFree (\prob -> p<<(ppr prob $$ text "RESULT: not solved yet")) work . simplify where
    work MZero = toHtml  "Don't know"
    work DontKnow{} = toHtml  "Don't know"
    work Success{..} =
       p
        << problem  +++ br +++
           procInfo +++ br +++
           divyes +++ thickbox res << spani "seeproof" << "(see proof)"

    work Fail{..} =
        p
        << problem +++ br +++
           procInfo +++ br +++
           divmaybe +++ thickbox res << spani "seeproof" << "(see failure)"

    work pr@Or{..} = p
                      << problem +++ br +++
                         procInfo +++ br +++
                          "Problem was translated to " +++ show(length subProblems) +++ " equivalent alternatives" +++ br +++
                          H.unordList subProblems
    work (And proc prob sub) =
        p
        << prob +++ br +++
           proc +++ br +++
--           "Problem was divided in " +++ show(length sub) +++ " subproblems" +++ br +++
           H.unordList sub
    work (MPlus p1 p2)  = p2 -- If we see the choice after simplifying, it means that none was successful
    work Step{..} = p
                    << problem +++ br +++ procInfo +++ br +++ subProblem

instance (HashConsed f, TRS.Ppr f) =>  HTMLTABLE (Rule f) where
    cell (lhs :-> rhs ) = td ! [theclass "lhs"]   << show lhs <->
                          td ! [theclass "arrow"] << (" " +++ H.primHtmlChar "#x2192" +++ " ") <->
                          td ! [theclass "rhs"]   << show rhs


instance HTMLTABLE Prolog.Clause where
    cell = cell . (td <<) .  show . Prolog.ppr
{-
    cell (h :- bb) = td ! [theclass "head"]  << show h <->
                     td ! [theclass "arrow"] << " :- " <->
                     td ! [theclass "body"]   << bb
-}

instance HTML Prolog.Pred where
    toHtml = toHtml . show . Prolog.ppr

typClass typ | isFullNarrowing typ = theclass "NDP"
typClass typ | isBNarrowing typ = theclass "BNDP"
typClass Rewriting = theclass "DP"
typClass Prolog    = theclass "Prolog"

divi ident = H.thediv ! [H.theclass ident]
spani ident = H.thespan ! [H.theclass ident]
divresult = spani "result" << "RESULT: "
divyes    = divresult +++ spani "yes" << "YES. "
divmaybe  = divresult +++ spani "maybe" << "Fail. "
thickbox thing c | label <- hashHtml thing =
         thediv ! [H.identifier ("tb"++label), H.thestyle "display:none"] << p << thing +++
         H.hotlink ("#TB_inline?height=600&width=600&inlineId=tb" ++ label) ! [theclass "thickbox"] << c

hashHtml = show . abs . hashString . H.renderHtml

-- ----------------------
-- dumb console logs
-- ----------------------
pprSkelt = foldFree ppr f where
  f Success{}      = text "success"
  f Fail{}         = text "failure"
  f MZero          = text "[]"
  f DontKnow{}     = text "don't know"
  f (And _ _ pp)   = parens $ cat $ punctuate (text " & ") pp
  f (Or _ _ pp)    = parens $ cat $ punctuate (text " | ") pp
  f (MPlus p1 p2)  = p1 <+> text " | " <+> p2
  f Step{..}       = text " -> " <> subProblem

-- instance H.ADDATTRS H.HotLink where h ! aa = h{H.hotLinkAttributes = H.hotLinkAttributes h ++ aa}