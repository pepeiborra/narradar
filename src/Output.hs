{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Output where

import Control.Applicative
import Control.Monad.Free
import Data.HashTable (hashString)
import Data.Foldable
import qualified Data.Map as Map
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
import TRS.Utils (snub)

import Prelude hiding (concat)
-- ----
-- TPDB
-- ----

pprTPDB :: forall f. Problem f -> String
pprTPDB p@(Problem _ trs@TRS{} dps@TRS{} ) =
  unlines [ printf "(VAR %s)" (unwords $ map (show . pprTerm) $ snub $ foldMap3 vars' ( rules <$> p))
          , printf "(PAIRS\n %s)" (unlines (map (show.pprRule) (rules dps)))
          , printf "(RULES\n %s)" (unlines (map (show.pprRule) (rules trs)))]

  where pprRule (a:->b) = pprTerm a <+> text "->" <+> pprTerm b
        pprTerm (open -> Just v@Var{})   = ppr (inject v)
        pprTerm (open -> Just (T (id::Identifier) [])) = text (show id)
        pprTerm (open -> Just (T (id::Identifier) tt)) =
            text (show id) <> parens (cat$ punctuate comma$ map pprTerm tt)
--        pprTerm _ = Text.PrettyPrint.empty

-------------------
-- Ppr
-------------------

class Ppr a where ppr :: a -> Doc

instance (Functor f, Foldable f, Ppr x) => Ppr (f x) where ppr = brackets . vcat . punctuate comma . toList . fmap ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance Show (Term a) => Ppr (Rule a) where ppr = text . show
instance TRS.Ppr f => Ppr (TRS id f) where ppr trs@TRS{} = ppr $ rules trs
instance Ppr Int where ppr = int

instance TRS.Ppr f => Ppr (Term f) where ppr = TRS.ppr
instance Ppr ProblemType where
    ppr typ | isFullNarrowing typ = text "NDP"
    ppr typ | isBNarrowing typ    = text "BNDP"
    ppr Rewriting = text "DP"

instance TRS.Ppr a => Ppr (Problem a) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps


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

instance Ppr ProcInfo where ppr = text . show
--------------
-- HTML
-------------

instance HTML a => HTMLTABLE a where cell = cell . toHtml

instance HTML AF.AF where
    toHtml (AF.AF af) = H.unordList [ pi +++ "(" +++ show k +++ ") = " +++ show ii  | (k,ii) <- Map.toList af]
        where pi = H.primHtmlChar "pi"

instance HTML Doc where toHtml = toHtml . show

instance HTML ProcInfo where
    toHtml (AFProc af Nothing)    = "PROCESSOR: " +++ "Argument Filtering " +++ af
    toHtml (AFProc af (Just div)) = "PROCESSOR: " +++ "Argument Filtering " +++ af +++ showParen True (shows div) ""
    toHtml DependencyGraph{} = "PROCESSOR: " +++ "Dependency Graph (cycle)"
    toHtml Polynomial      = "PROCESSOR: " +++ "Polynomial Interpretation"
    toHtml NarrowingP      = "PROCESSOR: " +++ "Narrowing Processor"
    toHtml (External e)    = "PROCESSOR: " +++ "External - " +++ show e

instance TRS.Ppr f => HTML (Problem f) where
    toHtml (Problem typ  trs@TRS{} dps) | null $ rules dps =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules"</> aboves (rules trs) </>
                 "Dependency Pairs: none")
    toHtml (Problem typ trs@TRS{} dps@TRS{}) =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules" </>
                 aboves (rules trs) </>
            H.td ! [H.theclass "DPS" ] << "Dependency Pairs" </>
                 aboves (rules dps))

instance TRS.Ppr f => HTML (ProblemProof Html f) where
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

instance (HashConsed f, T Identifier :<: f, TRS.Ppr f) =>  HTMLTABLE (Rule f) where
    cell (lhs :-> rhs ) = td ! [theclass "lhs"]   << show lhs <->
                          td ! [theclass "arrow"] << (" " +++ H.primHtmlChar "#x2192" +++ " ") <->
                          td ! [theclass "rhs"]   << show rhs

typClass typ | isFullNarrowing typ = theclass "NDP"
typClass typ | isBNarrowing typ = theclass "BNDP"
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
  f (MPlus p1 p2) = p1 <+> text " | " <+> p2

-- instance H.ADDATTRS H.HotLink where h ! aa = h{H.hotLinkAttributes = H.hotLinkAttributes h ++ aa}