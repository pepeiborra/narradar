{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Proof where

import Control.Applicative
import Control.Arrow
import Control.Exception (assert)
import Control.Monad as M
import Control.Monad.Logic as M
import Control.Monad.State as M
import Control.Monad.RWS
import qualified  "monad-param" Control.Monad.Parameterized as MonadP
import qualified  "monad-param" Control.Monad.MonadPlus.Parameterized as MonadP
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), toList, maximum, sum)
import Data.IORef
import Data.List (unfoldr)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Data.Traversable as T
import Text.PrettyPrint hiding ()
import Text.XHtml (Html, toHtml)
import System.IO.Unsafe

import qualified Language.Prolog.Syntax as Prolog (Program)
import qualified TRS as TRS

import Narradar.Types hiding (dropNote)
import Narradar.Utils
import qualified Narradar.ArgumentFiltering as AF

import Control.Monad.Free

import Prelude hiding (maximum, sum, log, mapM, foldr, concatMap)
import qualified Prelude as P
-- ---------
-- Proofs
-- ---------

data ProofF s k =
    And     {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Or      {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Step    {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblem::k}
  | Stage k
  | Success {procInfo :: !(SomeInfo), problem :: !(SomeProblem), res::s}
  | Fail    {procInfo :: !(SomeInfo), problem :: !(SomeProblem), res::s}
  | DontKnow{procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | MPlus k k
  | MPlusPar k k
  | MZero
  | MAnd  k k
  | MDone

type Proof s a            = Free (ProofF s) a
type ProblemProof     s f = Proof s (Problem f)
type ProblemProofG id s f = Proof s (ProblemG id f)


success  pi p0 s = jail $ htmlProofF (Success (someInfo pi) (someProblem p0) s)
success' pi p0 s = jail $ htmlProofF (Success pi p0 s)
failP    pi p0 s = jail $ htmlProofF (Fail (someInfo pi) (someProblem p0) s)
failP'   pi p0 s = jail $ htmlProofF (Fail pi p0 s)
choiceP  p1 p2   = jail $ htmlProofF (MPlus p1 p2)
dontKnow pi p0   = jail $ htmlProofF (DontKnow (someInfo pi) (someProblem p0))
dontKnow' pi p0  = jail $ htmlProofF (DontKnow pi p0)
andP pi p0 []    = success pi p0 mempty
andP pi p0 pp    = jail $ htmlProofF (And (someInfo pi) (someProblem p0) pp)
andP' pi p0 []   = success' pi p0 mempty
andP' pi p0 pp   = jail $ htmlProofF (And pi p0 pp)
orP  pi p0 []    = success pi p0 mempty
orP  pi p0 pp    = jail $ htmlProofF (Or (someInfo pi) (someProblem p0) pp)
orP' pi p0 []    = success' pi p0 mempty
orP' pi p0 pp    = jail $ htmlProofF (Or pi p0 pp)
step pi p0 p     = jail $ htmlProofF (Step (someInfo pi) (someProblem p0) (return p))
step' pi p0 p    = jail $ htmlProofF (Step pi p0 p)
mand p1 p2       = jail $ htmlProofF (MAnd p1 p2)
mdone            = jail $ htmlProofF MDone
mall             = foldr mand mdone
mplusPar p1 p2   = jail $ htmlProofF (MPlusPar p1 p2)
msumPar          = foldr mplusPar mzero
stage            = jail . htmlProofF . Stage

htmlProofF :: ProofF Html a -> ProofF Html a
htmlProofF = id

htmlProof :: Proof Html a -> Proof Html a
htmlProof = id

deriving instance (Show s, Show k) => Show (ProofF s k)

data SomeProblem where
    SomeProblem       :: (TRSC f, T id :<: f, Ord id, Show id) => !(ProblemG id f) -> SomeProblem
--    SomePrologProblem :: [Goal] -> Prolog.Program -> SomeProblem

instance Show SomeProblem where
    show (SomeProblem p) = "<some problem>"
--    show (SomePrologProblem gg pgm) = show (PrologProblem Prolog gg pgm :: Problem BasicId)

instance Ppr SomeProblem where
  ppr (SomeProblem p@(Problem typ TRS{} _)) = ppr p
--  ppr (SomePrologProblem gg cc) = ppr (mkPrologProblem gg cc)

someProblem :: (TRSC f, T id :<: f, Ord id, Show id) => ProblemG id f -> SomeProblem
someProblem p@Problem{}      = SomeProblem (trimProblem p)
--someProblem (PrologProblem typ gg pgm) = SomePrologProblem gg pgm
trimProblem (Problem typ trs dps) = Problem typ trs (tRS $ rules dps)


data SomeInfo where SomeInfo :: Show id => !(ProcInfo id) -> SomeInfo
instance Ppr SomeInfo where ppr (SomeInfo pi) = ppr pi
instance Show SomeInfo where show = show . ppr

someInfo = SomeInfo

instance TRS.Ppr a => Ppr (ProblemProof String a) where
    ppr = foldFree leaf f where
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

-- -------------------
-- MonadPlus instances
-- -------------------

instance MonadP.MonadZero (Free (ProofF s)) where mzeroM = Impure MZero
instance MonadP.MPlus (Free (ProofF s)) (Free (ProofF s)) (Free (ProofF s))  where
    mplus p1 p2 = Impure (MPlus p1 p2) -- if isSuccess p1 then p1 else choiceP p1 p2


-- ------------------
-- Monad Transformer
-- ------------------
-- we are going to need a monad transformer (for the Aprove proc)

type ProofT   s m a = FreeT (ProofF s) m a
type PPT id f s m   = ProofT s m (ProblemG id f)

liftProofT :: P.Monad m => Proof s a -> ProofT s m a
liftProofT = wrap

instance P.Monad m => MonadP.MonadZero (FreeT (ProofF s) m) where mzeroM = wrap(Impure MZero)
instance Monad m => MonadP.MPlus (FreeT (ProofF s) m) (FreeT (ProofF s) m) (FreeT (ProofF s) m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus m1 m2)

-- Additional parameterized instances between the Proof and ProofT
instance (P.Monad m, MonadP.Monad m) => MonadP.MPlus (Free (ProofF s)) (FreeT (ProofF s) m) (FreeT (ProofF s) m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus (wrap m1) m2)

instance (P.Monad m, MonadP.Monad m) => MonadP.MPlus (FreeT (ProofF s) m) (Free (ProofF s)) (FreeT (ProofF s) m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus  m1 (wrap m2))

-- ------------
-- * Evaluators
-- ------------

type StagedProof s a  = Proof s (Proof s a)

stageProof :: forall a s. Proof s a -> StagedProof s a
stageProof = foldFree (return . return) f where
  f (Stage p) = return (unstageProof p)
  f x = Impure x

unstageProof :: StagedProof s a -> Proof s a
unstageProof = join

runProof :: (Monoid s) => Proof s a -> Maybe (Proof s b)
runProof p = listToMaybe $ observeMany 1 $ do
  sol <- foldFree return evalF (stageProof p)
--  let sol' = unstageProof sol
  runProofDirect sol
 where
  runProofDirect = foldFree (const mzero) evalF
{-
runProofBFS :: (Monoid s) => Proof s a -> Maybe (Proof s b)
runProofBFS t = listToMaybe $ observeMany 1 (msum (foldFree (const mzero) evalF <$> tt)) where
  tt = map fst $ takeWhile (not.snd) $ map (`cutProof` ann_t) [1..]
  cutProof depth = (`runState` True)
                  . foldFreeM (return . Pure)
                              (\(Annotated n u) -> if  n<=depth then return (Impure u)
                                                                else put False >> return mzero)
  ann_t = annotateLevel t
-}
--evalF :: forall mp mf s a. (Functor mp, MonadPlus mp, MonadFree (ProofF s) mf) => ProofF s (mp (mf a)) -> mp (mf a)
evalF :: forall mp s a. (Functor mp, MonadLogic mp) => ProofF s (mp (Proof s a)) -> mp (Proof s a)
evalF Fail{}         = mzero
evalF DontKnow{}     = mzero
evalF MZero          = mzero
evalF Success{..}    = return (jail (fixS Success{..}))                where fixS :: ProofF s x -> ProofF s x;fixS = id
evalF MDone          = return (jail (fixS MDone))                      where fixS :: ProofF s x -> ProofF s x;fixS = id
evalF (MPlus p1 p2)  = p1 `M.mplus` p2
evalF (MPlusPar p1 p2) = p1 `M.interleave` p2
evalF (And pi pb ll) = (jail . fixS . And  pi pb) <$> P.sequence ll    where fixS :: ProofF s x -> ProofF s x;fixS = id;
evalF (Or  pi pb ll) = (jail . fixS . Step pi pb) <$> msum ll          where fixS :: ProofF s x -> ProofF s x;fixS = id
evalF (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                       return (jail $ fixS $ MAnd s1 s2)               where fixS :: ProofF s x -> ProofF s x;fixS = id
evalF (Step pi pb p) = (jail . fixS . Step pi pb) <$> p                where fixS :: ProofF s x -> ProofF s x;fixS = id
evalF (Stage  p) = p

sequencePar []     = return []
sequencePar (x:xx) = x >>- \x' -> (x':) `liftM` sequencePar xx

unsafeUnwrapIO :: Functor f => FreeT f IO a -> Free f a
unsafeUnwrapIO (FreeT m) = go (unsafePerformIO m) where
  go (Left  a) = Pure a
  go (Right f) = Impure (unsafeUnwrapIO <$> f)


isSuccess :: Monoid s => Proof s k -> Bool
isSuccess' t = let res =foldFree (return False) isSuccessF t in res -- assert (res == isSuccess' t) res
isSuccess p = let res = isJust (runProof p)
              in assert (res == isSuccess' p) res

isSuccessF :: ProofF s Bool -> Bool
isSuccessF Fail{}         = False
isSuccessF Success{}      = True
isSuccessF DontKnow{}     = False
isSuccessF (And _ _ ll)   = and ll
isSuccessF (Or  _ _ [])   = True  -- HEADS UP unstandard
isSuccessF (Or  _ _ ll)   = or ll
isSuccessF (MPlus p1 p2)  = p1 || p2
--isSuccessF (MPlusPar p1 p2) = p1 || p2
isSuccessF MZero          = False
isSuccessF (MAnd  p1 p2)  = p1 && p2
isSuccessF MDone          = True
isSuccessF (Step _ _ p)   = p
isSuccessF (Stage p)      = p

-- isSuccessT = foldFreeT (const $ returnM False) (returnM.isSuccessF)

logLegacy proc prob Nothing    = failP proc prob (toHtml "Failed")
logLegacy proc prob (Just msg) = success proc prob msg

annotateLevel :: forall f a. (Functor f) => Free f a -> Free (AnnotatedF Int f) a
annotateLevel = go 0 where
  go i (Pure  x) = Pure x
  go i (Impure x) = Impure (Annotated i $ fmap (go (succ i)) x)

-- -----------------
-- Functor instances
-- -----------------
instance Foldable (ProofF s) where foldMap = T.foldMapDefault
$(derive makeFunctor     ''ProofF)
$(derive makeTraversable ''ProofF)
