{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Narradar.Output where

import Control.Applicative
import Control.Monad.Free.Narradar
import Data.ByteString.Char8 (unpack)
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

import qualified Narradar.ArgumentFiltering as AF
import Narradar.Proof
import Narradar.Types hiding ((!))
import qualified Narradar.Types as TRS
import Narradar.Utils (snub, foldMap3)
import Data.Term.Ppr

import qualified Language.Prolog.Syntax as Prolog

import Prelude hiding (concat)

--------------
-- HTML
-------------

instance HTML a => HTMLTABLE a where cell = cell . toHtml

instance Ppr id => HTML (AF.AF_ id) where
    toHtml (AF.AF af) = H.unordList [ pi +++ "(" +++ show(ppr k) +++ ") = " +++ show (Set.toList ii)
                                          | (k,ii) <- Map.toList af]
        where pi = H.primHtmlChar "pi"

instance HTML Doc where toHtml = toHtml . show

instance Ppr id => HTML (ProcInfo id) where
    toHtml (GroundOne af)    = "PROCESSOR: " +++ "ICLP'08 AF Processor " +++ maybe noHtml toHtml af
    toHtml (GroundAll af)    = "PROCESSOR: " +++ "ICLP'08 AF Processor (dumb SCC version) " +++ maybe noHtml toHtml af
    toHtml (ReductionPair af _)= "PROCESSOR: " +++ "ICLP'08 AF Processor for SCCs" +++ maybe noHtml toHtml af
    toHtml (EVProc af)       = "PROCESSOR: " +++ "Eliminate Extra Vars " +++ af
    toHtml DependencyGraph{} = "PROCESSOR: " +++ "Dependency Graph (cycle)"
    toHtml NoPairs{}         = "PROCESSOR: " +++ "Dependency Graph"
    toHtml (External e _)    = "PROCESSOR: " +++ "External - " +++ show e
    toHtml InstantiationP{}  = "PROCESSOR: " +++ "Graph Transformation via Instantiation"
    toHtml FInstantiationP{} = "PROCESSOR: " +++ "Graph Transformation via Forward Instantiation"
    toHtml NarrowingP{}      = "PROCESSOR: " +++ "Graph Transformation via Narrowing"
    toHtml NonTerminationLooping = "PROCESSOR: " +++ "Trivial non-termination"
    toHtml p                     = "PROCESSOR: " +++ show (ppr p)

--instance HTML Prolog.Program where toHtml = show . Prolog.ppr
instance (Ord v, Ord id, Ppr v, Ppr id) => HTML (Problem id v) where
    toHtml (Problem typ@Prolog{..} _ _) =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Clauses" </> aboves' program)
    toHtml (Problem typ trs dps@TRS{}) | null $ rules dps =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules"</> aboves' (rules trs) </>
                 "Dependency Pairs: none")
    toHtml (Problem typ trs dps@TRS{}) =
        H.table ! [typClass typ] << (
            H.td ! [H.theclass "problem"] << H.bold (toHtml (ppr typ <+> text "Problem")) </>
            H.td ! [H.theclass "TRS_TITLE" ] << "Rules" </>
                 aboves' (rules trs) </>
            H.td ! [H.theclass "DPS" ] << "Dependency Pairs" </>
                 aboves' (rules dps))

aboves' [] = cell noHtml
aboves' xx = aboves xx

instance HTML SomeProblem where
    toHtml (SomeProblem p@Problem{}) = toHtml p
--    toHtml (SomePrologProblem gg cc) = toHtml (mkPrologProblem gg cc)

instance HTML SomeInfo where toHtml (SomeInfo pi) = toHtml pi

instance (Ord id, Ppr id, Ppr v, Ord v) => HTML (ProblemProof id v) where
   toHtml = foldFree (\prob -> p<<(ppr prob $$ text "RESULT: not solved yet")) work where
    work MZero       = toHtml  "Don't know"
    work DontKnow{}  = toHtml  "Don't know"
    work Success{..} =
       p
        << problem  +++ br +++
           procInfo +++ br +++
           divyes +++ detailResult procInfo

    work Fail{..} =
        p
        << problem  +++ br +++
           procInfo +++ br +++
           divmaybe +++ detailResult procInfo
--           divmaybe +++ thickbox res << spani "seeproof" << "(see failure)"

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
    work (MAnd p1 p2) =
        p
        << H.unordList [p1,p2]
    work MDone = noHtml -- toHtml "RESULT: D"
    work (MPlus    p1 p2)  = p2 -- If we see the choice after simplifying, it means that none was successful
    work (MPlusPar p1 p2)  = p2 -- If we see the choice after simplifying, it means that none was successful
    work (Stage p)= p
    work Step{..} = p
                    << problem +++ br +++ procInfo +++ br +++ subProblem

    detailResult :: SomeInfo -> Html
    detailResult (SomeInfo (External _ (find isOutputHtml -> Just (OutputHtml (unpack -> output))))) =
       thickbox output << spani "seeproof" << "(see proof)"
    detailResult _ = noHtml


instance (Ppr (Term t v)) =>  HTMLTABLE (Rule t v) where
    cell (lhs :-> rhs ) = td ! [theclass "lhs"]   << show (ppr lhs) <->
                          td ! [theclass "arrow"] << (" " +++ H.primHtmlChar "#x2192" +++ " ") <->
                          td ! [theclass "rhs"]   << show (ppr rhs)


instance (Ppr id) => HTMLTABLE (Prolog.Clause id) where
    cell = cell . (td <<) .  show . ppr
{-
    cell (h :- bb) = td ! [theclass "head"]  << show h <->
                     td ! [theclass "arrow"] << " :- " <->
                     td ! [theclass "body"]   << bb
-}

instance (Ppr id) => HTML (Prolog.Goal id) where
    toHtml = toHtml . show . ppr

typClass typ | isFullNarrowing typ = theclass "NDP"
typClass typ | isBNarrowing typ = theclass "BNDP"
typClass typ | isGNarrowing typ = theclass "GNDP"
typClass typ | isRewriting typ  = theclass "DP"
typClass Prolog{}  = theclass "Prolog"

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