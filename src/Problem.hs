{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs#-}
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
import Operad
import TaskPoolSTM
import qualified ArgumentFiltering as AF

import Prelude as P hiding (log, mapM, foldr, concatMap, Monad(..), (=<<))

data Progress_ f s a =
    NotDone a
  | And     {procInfo::ProcInfo, problem::Problem f, subProblems::[Progress_ f s a]}
  | Or      {procInfo::ProcInfo, problem::Problem f, subProblems::[Progress_ f s a]}
  | Success {procInfo::ProcInfo, problem::Problem f, res::s}
  | Fail    {procInfo::ProcInfo, problem::Problem f, res::s}
  | DontKnow{procInfo::ProcInfo, problem::Problem f}
  | Choice (Progress_ f s a) (Progress_ f s a)
  | MZero
     deriving (Show)

type ProblemProgress s f = Progress_ f s (Problem f)

success = Success
failP   = Fail

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

instance Foldable (Progress_ f s) where foldMap = foldMapDefault
$(derive makeFunctor     ''Progress_)
$(derive makeTraversable ''Progress_)
-- $(derive makeNFData      ''Progress_)

-- Progress is a monad (obvious in retrospect, but I didn't notice at the beginning)
instance Return (Progress_ f s) where returnM = NotDone
instance Bind (Progress_ f s) (Progress_ f s) (Progress_ f s) where xs >>= f = join (fmap f xs)
instance Fail (Progress_ f s) where fail = error

instance MonadZero (Progress_ f s) where mzeroM = MZero
instance MPlus (Progress_ f s) (Progress_ f s) (Progress_ f s) where
    p1 `mplus` p2 = if isSuccess p1 then p1 else Choice p1 p2

-- But we are going to need a monad transformer (for the Aprove proc)
-- This fancy monad transformer allows IO computations in parallel. Cool huh? :)
data ProgressT_ f s m a where
    ProgressT :: m (Progress_ f s a) -> ProgressT_ f s m a
    Par       :: IO(Progress_ f s a) -> ProgressT_ f s IO a

runProgressT :: ProgressT_ f s m a -> m(Progress_ f s a)
runProgressT (ProgressT x) = x
runProgressT (Par       x) = x

m ||>= f = Par m >>= f
(>||>) :: forall m s a b c f .  (Bind m (ProgressT_ f s IO) (ProgressT_ f s IO)) =>
         (a -> m b) -> (b -> ProgressT_ f s IO c) -> (a -> ProgressT_ f s IO c)
f >||> g  = \a -> Par (runProgressT $ (f >=> returnPPT) a) >>= g
           where returnPPT :: a' -> ProgressT_ f s IO a'
                 returnPPT = returnM

type    PPT s m a = ProgressT_ a s m (Problem a)

instance Monad m => Functor (ProgressT_ f s m) where
    fmap f (ProgressT x) = ProgressT $ liftM (fmap f) x
    fmap f (Par x)       = ProgressT $ liftM (fmap f) x

instance Monad m => Return (ProgressT_ f s m) where returnM = ProgressT . returnM . NotDone
instance Monad m => Bind  (ProgressT_ f s m) (ProgressT_ f s m) (ProgressT_ f s m) where
    Par xs >>= f = bindPar xs f where
       bindPar p f = ProgressT $ liftM unE $ do
         sol <- p
         let (EM (MO op xx)) = fmap (liftM inE . runProgressT . f) (inE sol)
         xx' <- parSequence 4 xx
         return (join (EM(MO op xx')))

    xs     >>= f = ProgressT (runProgressT xs >>= concatMapMP (runProgressT . f))

instance Fail (ProgressT_ f s m) where fail = error

-- If the below instance was definible, we would have no need for MonadTrans
--  Unfortunately, this conflicts with the definition of MZero, as afaik there
--  is no way to specify an ordering between type equations here :(

--instance Monad m => Bind m        (ProgressT_ f s m) (ProgressT_ f s m) where m >>= f = (liftPPT m `asTypeOf1` f undefined) >>= f

instance MonadTrans (ProgressT_ f s) where lift = liftPPT

liftPPT :: Monad m => m a -> ProgressT_ f s m a
liftPPT = ProgressT . liftM NotDone

instance Monad m => Bind (Progress_ f s) (ProgressT_ f s m) (ProgressT_ f s m) where xs >>= f = (liftProgressT xs `asTypeOf1` f undefined ) >>= f
instance Monad m => Bind (ProgressT_ f s m) (Progress_ f s) (ProgressT_ f s m) where xs >>= f = let liftF x = liftProgressT x `asTypeOf1` xs in xs >>= (liftF.f)

instance Monad m => MonadZero (ProgressT_ f s m) where mzeroM = ProgressT (returnM MZero)
instance Monad m => MPlus  (ProgressT_ f s m) (ProgressT_ f s m) (ProgressT_ f s m) where
    p1 `mplus` p2 = ProgressT $ do
                      s1 <- runProgressT p1
                      if isSuccess s1 then returnM s1 else runProgressT p2 >>= \s2 -> return (Choice s1 s2)

liftProgressT :: Monad m => Progress_ f s a -> ProgressT_ f s m a
liftProgressT = ProgressT . returnM


{-# RULES "Progress join" join = Problem.joinP #-}
joinP :: Progress_ f s (Progress_ f s a) -> Progress_ f s a
joinP (NotDone p)    = p
joinP (And pi pr pp) = And pi pr (map joinP pp)
joinP (Or  pi pr pp) = Or  pi pr (map joinP pp)
joinP MZero          = MZero
joinP DontKnow{..}   = DontKnow{..}
joinP Success{..}    = Success{..}
joinP Fail{..}       = Fail{..}
joinP (Choice p1 p2) = Choice (joinP p1) (joinP p2)

instance SignatureC (Problem f) Identifier where getSignature (Problem _ trs@TRS{} dps@TRS{}) = sig trs `mappend` sig dps -- getSignature (trs `mappend` dps)

isSuccess :: Progress_ f s a -> Bool
isSuccess NotDone{} = False
isSuccess Fail{}    = False
isSuccess Success{} = True
isSuccess DontKnow{}= False
isSuccess (And _ _ ll)  = P.all isSuccess ll
isSuccess (Or  _ _ ll)  = P.any isSuccess ll
isSuccess MZero     = False
isSuccess (Choice p1 p2) = isSuccess p1 || isSuccess p2

type PP_ f s = EfficientMonad (Progress_ f s)
type PP  s a = PP_ a s (Problem a)
instance (M.Monad m, Traversable m) => Return (EfficientMonad m) where returnM = M.return
instance Fail (EfficientMonad m) where fail = error
instance (M.Monad m, Traversable m) => Bind (EfficientMonad m) (EfficientMonad m) (EfficientMonad m) where (>>=) = (M.>>=)

--solveProblem :: (Problem a -> ProblemProgress s a) -> PP s a -> PP s a
--solveProblem f m =  (inE . f) =<< m 
solveProblem = (=<<)

runPP :: PP s a -> ProblemProgress s a
runPP = unE
{-
class Monad m => SolveProblemM m where
  --solveProblemM :: (Problem a -> m (ProblemProgress s a)) -> PP s a -> m (PP s a)
  --solveProblemM f = concatMapM (M.liftM inE . f)
    solveProblemM :: (Problem a -> m (ProblemProgress s a)) -> ProblemProgress s a -> m(ProblemProgress s a)
    solveProblemM = concatMapM

instance SolveProblemM IO where
  solveProblemM f = concatMapM (unsafeInterleaveIO {-. M.liftM inE -}. f)

solveProblemMPar f p = fmap runPP $ do
    let (EM (MO op xx)) = fmap (M.liftM inE . f) (inE p)
    xx' <- liftIO $ parSequence 4 xx
    return (join (EM(MO op xx')))
-}

slice = everywhere simplifyAll where
 simplifyAll x | Just x' <- simplify x = simplifyAll x'
               | otherwise = x

everywhere f x@Or{..} = x{subProblems = map f subProblems}
everywhere f x@And{..} = x{subProblems = map f subProblems}
everywhere f (Choice p1 p2) = Choice (f p1) (f p2)
everywhere f x = x

simplify :: ProblemProgress s f -> Maybe (ProblemProgress s f)
simplify p@(Or  _ _ aa) | isSuccess p = listToMaybe [p | p <- aa, isSuccess p]
simplify   (Or  _ p []) = Just (NotDone p)
simplify   (And p f []) = error "simplify: unexpected"
simplify   (Choice p1 p2)
    | isSuccess p1 = Just p1
    | isSuccess p2 = Just p2
    | otherwise    = Just MZero
simplify _ = Nothing

logLegacy proc prob Nothing    = failP proc prob "Failed"
logLegacy proc prob (Just msg) = success proc prob msg

pprSkelt Success{} = text "success"
pprSkelt Fail{}    = text "failure"
pprSkelt NotDone{} = text "not done"
pprSkelt MZero     = text "don't know"
pprSkelt DontKnow{}= text "don't know"
pprSkelt (And _ _ pp) = parens $ cat $ punctuate (text " & ") $ map pprSkelt pp
pprSkelt (Or _ _ pp)  = parens $ cat $ punctuate (text " | ") $ map pprSkelt pp
pprSkelt (Choice p1 p2) = pprSkelt p1 <+> text " | " <+> pprSkelt p2

pprTPDB :: TRS.Ppr f => Problem f -> String
pprTPDB (Problem _ trs@TRS{} dps@TRS{} ) =
  unlines [ printf "(VAR %s)" (unwords $ map (show . inject) $ snub $ P.concat (foldMap vars <$> rules trs))
          , printf "(PAIRS\n %s)" (unlines (map show (rules dps)))
          , printf "(RULES\n %s)" (unlines (map show (rules trs)))]

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
    ppr MZero = text "don't know"
    ppr (NotDone prob) = ppr prob $$
                         text ("RESULT: Not solved yet")
    ppr Success{..} =
        ppr problem $$
        text "PROCESSOR: " <> text (show procInfo) $$
        text ("RESULT: Problem solved succesfully") $$
        text ("Output: ") <>  (vcat . map text . lines) res
    ppr Fail{..} =
        ppr problem $$
        text "PROCESSOR: " <> (text.show) procInfo  $$
        text ("RESULT: Problem could not be solved.") $$
        text ("Output: ") <> (vcat . map text . lines) res
    ppr p@(Or proc prob sub)
      | Just res <- simplify p = ppr res
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
   toHtml = work . slice where
    work MZero = toHtml  "Don't know"
    work DontKnow{} = toHtml  "Don't know"
    work (NotDone prob) = p << prob
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

    work pr@Or{..}
        | Just res <- simplify pr = toHtml res
        | otherwise = p
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
    work (Choice p1 p2) | isSuccess p1 = work p1
                        | otherwise    = work p2

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