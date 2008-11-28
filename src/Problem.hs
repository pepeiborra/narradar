{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude, PackageImports #-}

module Problem where

import Control.Applicative
import qualified Control.Monad as M
import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import Data.List (intersperse)
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), toList)
import Data.HashTable (hashString)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Data.Traversable as T
import Text.Dot
import Text.PrettyPrint
import Text.Printf
import qualified Text.XHtml as H
import Text.XHtml (HTML(..), Html(..), (<<), (+++), (!), p, br, noHtml, theclass, hotlink, thediv
                  ,identifier,table,td)
import Text.XHtml.Table
import System.IO.Unsafe

import Types hiding (Ppr(..),ppr, (!))
import qualified Types as TRS
import Utils
import TaskPoolSTM
import qualified ArgumentFiltering as AF

import Control.Monad.Free
import Control.Monad.Operad

import Prelude as P hiding (log, mapM, foldr, concatMap, Monad(..), (=<<))

data ProgressF f (s :: *) k =
    And     {procInfo::ProcInfo, problem::Problem f, subProblems::[k]}
  | Or      {procInfo::ProcInfo, problem::Problem f, subProblems::[k]}
  | Success {procInfo::ProcInfo, problem::Problem f, res::s}
  | Fail    {procInfo::ProcInfo, problem::Problem f, res::s}
  | DontKnow{procInfo::ProcInfo, problem::Problem f}
  | Choice k k
  | MZero
     deriving (Show)

type Progress f s a     = Free (ProgressF f s) a
type ProblemProgress s f = Progress f s (Problem f)

success = ((Impure.).) . Success
failP   = ((Impure.).) . Fail
andP    = ((Impure.).) . And
orP     = ((Impure.).) . Or
choiceP = (Impure.)    . Choice
dontKnow= (Impure.)    . DontKnow

data ProcInfo = AFProc AF.AF
              | DependencyGraph
              | Polynomial
              | External ExternalProc
              | NarrowingP
     deriving (Eq)

instance Show ProcInfo where
    show DependencyGraph = "Dependency Graph Processor"
    show (External proc) = "External: " ++ show proc
    show NarrowingP      = "Narrowing Processor"
    show (AFProc af) | af == AF.empty = "AF processor"
                     | otherwise      =  show af
    show (Polynomial)    = "Polynomial ordering"

data ExternalProc = MuTerm | Aprove | Other String
     deriving (Eq, Show)

instance Foldable Problem_ where foldMap = foldMapDefault
$(derive makeFunctor     ''Problem_)
$(derive makeTraversable ''Problem_)

instance Foldable (ProgressF f s) where foldMap = foldMapDefault
$(derive makeFunctor     ''ProgressF)
$(derive makeTraversable ''ProgressF)

instance MonadZero (Free (ProgressF f s)) where mzeroM = Impure MZero
instance MPlus (Free (ProgressF f s)) (Free (ProgressF f s)) (Free (ProgressF f s))  where
    p1 `mplus` p2 = if isSuccess p1 then p1 else choiceP p1 p2

-- But we are going to need a monad transformer (for the Aprove proc among other things)
type ProgressT f s m a = FreeT (ProgressF f s) m a
type PPT       s m f   = ProgressT f s m (Problem f)

runProgressT  = unwrap

liftProgressT :: Monad m => Progress f s a -> ProgressT f s m a
liftProgressT = wrap

instance Monad m => MPlus (FreeT (ProgressF f s) m) (FreeT (ProgressF f s) m) (FreeT (ProgressF f s) m) where
    p1 `mplus` p2 = FreeT $ go $ do
                      s1  <- runProgressT p1
                      if isSuccess s1 then unFreeT(wrap s1)
                         else do s2  <- runProgressT p2
                                 unFreeT (wrap(choiceP s1 s2))

instance SignatureC (Problem f) Identifier where getSignature (Problem _ trs@TRS{} dps@TRS{}) = sig trs `mappend` sig dps -- getSignature (trs `mappend` dps)

isSuccess :: Progress f s k -> Bool
isSuccess = foldFree (const False) isSuccessF where

isSuccessF :: ProgressF f s Bool -> Bool
isSuccessF Fail{}         = False
isSuccessF Success{}      = True
isSuccessF DontKnow{}     = False
isSuccessF (And _ _ ll)   = and ll
isSuccessF (Or  _ _ ll)   = or ll
isSuccessF MZero          = False
isSuccessF (Choice p1 p2) =  p1 || p2


simplify :: ProblemProgress s f -> ProblemProgress s f
simplify = foldFree returnM f where
  f   (Or  pi p [])  = dontKnow pi p
  f p@(Or  _ _ aa)   = msum aa
  f   (And p f [])   = error "simplify: empty And clause (probably a bug in your code)"
  f p@(Choice p1 p2)
      | isSuccess p1 = p1
      | isSuccess p2 = p2
      | otherwise    = mzeroM
  f p                = Impure p

logLegacy proc prob Nothing    = failP proc prob "Failed"
logLegacy proc prob (Just msg) = success proc prob msg

pprSkelt = foldFree (const$ text "not done") f where
  f Success{}      = text "success"
  f Fail{}         = text "failure"
  f MZero          = text "don't know"
  f DontKnow{}     = text "don't know"
  f (And _ _ pp)   = parens $ cat $ punctuate (text " & ") pp
  f (Or _ _ pp)    = parens $ cat $ punctuate (text " | ") pp
  f (Choice p1 p2) = p1 <+> text " | " <+> p2

pprTPDB :: TRS.Ppr f => Problem f -> String
pprTPDB (Problem _ trs@TRS{} dps@TRS{} ) =
  unlines [ printf "(VAR %s)" (unwords $ map (show . inject) $ snub $ P.concat (foldMap vars <$> rules trs))
          , printf "(PAIRS\n %s)" (unlines (map show (rules dps)))
          , printf "(RULES\n %s)" (unlines (map show (rules trs)))]


pprTPDBdot :: TRS.Ppr f => Problem f -> String
pprTPDBdot (Problem _ trs@TRS{} dps@TRS{} ) =
  unlines [ "(VAR " ++ (unwords $ map (show . inject) $ snub $ P.concat (foldMap vars <$> rules trs)) ++ ")"
          , "(PAIRS\\l" ++ (unlines (map ((' ':).show) (rules dps))) ++ ")"
          , "(RULES\\l" ++ (unlines (map ((' ':).show) (rules trs))) ++ ")\\l"]
  where unlines = concat . intersperse "\\l"

instance Functor Dot where fmap = M.liftM

pprDot prb = showDot (foldFree trsnode' f (annotate (const False) isSuccess prb) =<< node [("label","0")]) where
    f (Annotated done Success{..})    par = trsnode problem done par >>= procnode procInfo >>= childnode [("label", "YES"), ("color","#29431C")]
    f (Annotated done Fail{..})       par = trsnode problem done par >>= procnode procInfo >>= childnode [("label", "NO"),("color","#60233E")]
    f (Annotated done MZero{})        par = childnode' [("label","Don't Know")] (doneEdge done) par
    f (Annotated done DontKnow{..})   par = trsnode problem done par >>= procnode procInfo >>= childnode [("label","Don't Know")]
    f (Annotated done (Choice p1 p2)) par = go$ do
        dis <- childnode' [("shape","point"),("label","")] (doneEdge done) par
        p1 dis
        p2 dis
        return dis
    f (Annotated done And{subProblems=[p], procInfo = proc@AFProc{}}) par
                         = procnode' proc done par >>= \me -> p me >> return me
    f (Annotated done And{subProblems=[p], ..}) par = f (Annotated done Or {subProblems = [p], ..}) par
    f (Annotated done And{..}) par = go$ do
                                trs <- trsnode problem done par
                                (nc,me) <- cluster $ go $ do
                                             attribute ("color", "#E56A90")
                                             me <- childnode [("label", show procInfo)] trs
                                             forM_ subProblems ($ me)
                                             return me
                                return me
    f (Annotated done Or{..})  par = go$ do
                                trs <- trsnode problem done par
                                me  <- childnode [("label", show procInfo)] trs
                                forM_ subProblems ($ me)
                                return me

trsLabel trs      = ("label", pprTPDBdot trs)
trsColor (Problem Narrowing _ _) = ("color", "#F97523")
trsColor (Problem Rewriting _ _) = ("color", "#60233E")
trsAttrs trs      = [trsLabel trs, trsColor trs, ("shape","box"), ("style","bold"),("fontname","monospace"),("fontsize","10"),("margin",".2,.2")]
trsnode  trs done = childnode'(trsAttrs trs) (doneEdge done)
trsnode' trs      = childnode (trsAttrs trs)
doneEdge True     = [("color", "green")]
doneEdge False    = [("color", "red")]

procnode  procInfo      = childnode  [("label", show procInfo)]
procnode' procInfo done = childnode' [("label", show procInfo)] (doneEdge done)

childnode attrs = childnode' attrs []
childnode' attrs edge_attrs par = node (("URL","url"):attrs) >>= \n -> edge par n edge_attrs >> return n

-------------------
-- Ppr
-------------------

class Ppr a where ppr :: a -> Doc

instance (Functor f, Foldable f, Ppr x) => Ppr (f x) where ppr = brackets . vcat . punctuate comma . toList . fmap ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance Show (Term a) => Ppr (Rule a) where ppr = text . show
instance TRS.Ppr f => Ppr (TRS id f) where ppr trs@TRS{} = ppr $ rules trs

instance Ppr ProblemType where
    ppr Narrowing = text "NDP"
    ppr Rewriting = text "DP"

instance TRS.Ppr a => Ppr (Problem a) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps


instance TRS.Ppr a => Ppr (ProblemProgress String a) where
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
    toHtml (AFProc af)     = "PROCESSOR: " +++ "Argument Filtering " +++ af
    toHtml DependencyGraph = "PROCESSOR: " +++ "Dependency Graph (cycle)"
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

instance TRS.Ppr f => HTML (ProblemProgress Html f) where
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
    work (Choice p1 p2)  = p2 -- If we see the choice after simplifying, it means that none was successful

instance (HashConsed f, T Identifier :<: f, TRS.Ppr f) =>  HTMLTABLE (Rule f) where
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

-- instance H.ADDATTRS H.HotLink where h ! aa = h{H.hotLinkAttributes = H.hotLinkAttributes h ++ aa}