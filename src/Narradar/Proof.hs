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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}

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
import Data.Array.IArray as A
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable (Foldable(..), toList, maximum, sum)
import Data.IORef
import Data.List (unfoldr, find)
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Data.Traversable as T
import Text.PrettyPrint as Doc
import Text.XHtml (Html, toHtml, noHtml)
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

data ProofF k =
    And     {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Or      {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblems::[k]}
  | Step    {procInfo :: !(SomeInfo), problem :: !(SomeProblem), subProblem::k}
  | Stage k
  | Success {procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | Fail    {procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | DontKnow{procInfo :: !(SomeInfo), problem :: !(SomeProblem)}
  | MPlus k k
  | MPlusPar k k
  | MZero
  | MAnd  k k
  | MDone

-- Unfortunately, GHC does not interpret type class constraints in type synonyms
-- in a useful way, at least here. In Proof and ProblemProofG we would wish that
-- the constraints are floated out to top, or at least to the nearest binding occurrence,
-- but instead they are kept, which means we cannot have these types in an impredicative position.
type ProofC a           = Free ProofF a
type Proof  a           = (MonadPlus m, MonadFree ProofF m) => m a
type ProblemProof  id f = ProofC (ProblemG id f)
type ProblemProofG id f = (MonadPlus m, MonadFree ProofF m) => m (ProblemG id f)
type ProblemProofC id f = ProofC (ProblemG id f)

success  pi p0 = jail (Success (someInfo pi) (someProblem p0))
success' pi p0 = jail (Success pi p0)
failP    pi p0 = jail (Fail (someInfo pi) (someProblem p0))
failP'   pi p0 = jail (Fail pi p0)
choiceP  p1 p2   = jail (MPlus p1 p2)
dontKnow pi p0   = jail (DontKnow (someInfo pi) (someProblem p0))
dontKnow' pi p0  = jail (DontKnow pi p0)
andP pi p0 []    = success pi p0
andP pi p0 pp    = jail (And (someInfo pi) (someProblem p0) pp)
andP' pi p0 []   = success' pi p0
andP' pi p0 pp   = jail (And pi p0 pp)
orP  pi p0 []    = success pi p0
orP  pi p0 pp    = jail (Or (someInfo pi) (someProblem p0) pp)
orP' pi p0 []    = success' pi p0
orP' pi p0 pp    = jail (Or pi p0 pp)
step pi p0 p     = jail (Step (someInfo pi) (someProblem p0) (return p))
step' pi p0 p    = jail (Step pi p0 p)
mand p1 p2       = jail (MAnd p1 p2)
mdone            = jail MDone
mall             = foldr mand mdone
mplusPar p1 p2   = jail (MPlusPar p1 p2)
msumPar          = foldr mplusPar mzero
stage            = jail . Stage

deriving instance (Show k) => Show (ProofF k)

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
someProblem p@(Problem typ trs _ ) = SomeProblem (trimProblem p)
--someProblem (PrologProblem typ gg pgm) = SomePrologProblem gg pgm

trimProblem (Problem typ trs (DPTRS dps_a _ _ _) ) = Problem typ trs (tRS$ A.elems dps_a)
trimProblem p = p


data SomeInfo where SomeInfo :: Show id => !(ProcInfo id) -> SomeInfo
instance Ppr SomeInfo where ppr (SomeInfo pi) = ppr pi
instance Show SomeInfo where show = show . ppr
someInfo = SomeInfo

instance TRS.Ppr f => Ppr (ProblemProofC id f) where
    ppr = foldFree leaf f where
      leaf prob = ppr prob $$ text ("RESULT: Not solved yet")
      f MZero = text "don't know"
      f Success{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        text ("RESULT: Problem solved succesfully") $$
        proofTail procInfo
      f Fail{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Problem could not be solved.") $$
        proofTail procInfo
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

      proofTail :: SomeInfo -> Doc
      proofTail (SomeInfo (External _ (find isOutputTxt -> Just (OutputTxt txt))))
                  = text ("Output: ") <> (vcat . map text . lines) txt
      proofTail _ = Doc.empty

-- -------------------
-- MonadPlus instances
-- -------------------

instance MonadP.MonadZero (Free ProofF) where mzeroM = jail MZero
instance MonadP.MPlus (Free ProofF) (Free ProofF ) (Free ProofF )  where
    mplus p1 p2 = jail $ MPlus p1 p2 -- if isSuccess p1 then p1 else choiceP p1 p2

instance MonadPlus (C (Free ProofF)) where
    mplus p1 p2 = jail $ MPlus p1 p2
    mzero       = jail MZero

-- ------------------
-- Monad Transformer
-- ------------------
-- we are going to need a monad transformer (for the Aprove proc)

type ProofT   m a = FreeT ProofF m a
type PPT id f m   = ProofT m (ProblemG id f)

liftProofT :: P.Monad m => ProofC a -> ProofT m a
liftProofT = wrap

instance P.Monad m => MonadP.MonadZero (FreeT ProofF m) where mzeroM = wrap(Impure MZero)
instance Monad m => MonadP.MPlus (FreeT ProofF m) (FreeT ProofF m) (FreeT ProofF m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus m1 m2)

-- Additional parameterized instances between the Proof and ProofT
instance (P.Monad m, MonadP.Monad m) => MonadP.MPlus (Free ProofF) (FreeT ProofF m) (FreeT ProofF m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus (wrap m1) m2)

instance (P.Monad m, MonadP.Monad m) => MonadP.MPlus (FreeT ProofF m) (Free ProofF) (FreeT ProofF m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus  m1 (wrap m2))

-- ------------
-- * Evaluators
-- ------------

--type StagedProof a  = Proof (Proof a)

--stageProof :: forall a s. Proof a -> StagedProof a
stageProof = foldFree (return . return) f where
  f (Stage p) = return (unstageProof p)
  f x = jail x

--unstageProof :: StagedProof a -> Proof a
unstageProof = join

runProof = runProof' . improve
--runProof' :: (Monoid s, MonadFree (ProofF s) proof) => ProofC a -> Maybe (proof b)
runProof' p = listToMaybe $ observeMany 1 search where
  p'     = stageProof p
  search = do
    sol <- foldFree return evalF p'
--  let sol' = unstageProof sol
    runProofDirect (sol `asTypeOf` p)

  runProofDirect p = foldFree (const mzero) evalF p `asTypeOf` search
{-
runProofBFS :: (Monoid s) => Proof a -> Maybe (Proof b)
runProofBFS t = listToMaybe $ observeMany 1 (msum (foldFree (const mzero) evalF <$> tt)) where
  tt = map fst $ takeWhile (not.snd) $ map (`cutProof` ann_t) [1..]
  cutProof depth = (`runState` True)
                  . foldFreeM (return . Pure)
                              (\(Annotated n u) -> if  n<=depth then return (Impure u)
                                                                else put False >> return mzero)
  ann_t = annotateLevel t
-}
--evalF :: forall mp mf a. (Functor mp, MonadPlus mp, MonadFree (ProofF s) mf) => ProofF (mp (mf a)) -> mp (mf a)
evalF :: forall mp a proof. (Functor mp, MonadLogic mp, MonadFree ProofF proof) => ProofF (mp (proof a)) -> mp (proof a)
evalF Fail{}         = mzero
evalF DontKnow{}     = mzero
evalF MZero          = mzero
evalF Success{..}    = return (jail Success{..})
evalF MDone          = return (jail MDone)
evalF (MPlus p1 p2)  = p1 `M.mplus` p2
evalF (MPlusPar p1 p2) = p1 `M.interleave` p2
evalF (And pi pb ll) = (jail . And  pi pb) <$> P.sequence ll
evalF (Or  pi pb ll) = (jail . Step pi pb) <$> msum ll
evalF (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                       return (jail $ MAnd s1 s2)
evalF (Step pi pb p) = (jail . Step pi pb) <$> p
evalF (Stage  p) = p

sequencePar []     = return []
sequencePar (x:xx) = x >>- \x' -> (x':) `liftM` sequencePar xx

unsafeUnwrapIO :: Functor f => FreeT f IO a -> Free f a
unsafeUnwrapIO (FreeT m) = go (unsafePerformIO m) where
  go (Left  a) = return a
  go (Right f) = jail (unsafeUnwrapIO <$> f)


--isSuccess :: Monoid s => ProofCk -> Bool
isSuccess' t = let res =foldFree (return False) isSuccessF t in res -- assert (res == isSuccess' t) res
isSuccess p = isJust (runProof' p `asTypeOf` Just p)

isSuccessF :: ProofF Bool -> Bool
isSuccessF Fail{}         = False
isSuccessF Success{}      = True
isSuccessF DontKnow{}     = False
isSuccessF (And _ _ ll)   = and ll
isSuccessF (Or  _ _ [])   = True  -- HEADS UP unstandard
isSuccessF (Or  _ _ ll)   = or ll
isSuccessF (MPlus p1 p2)  = p1 || p2
isSuccessF (MPlusPar p1 p2) = p1 || p2
isSuccessF MZero          = False
isSuccessF (MAnd  p1 p2)  = p1 && p2
isSuccessF MDone          = True
isSuccessF (Step _ _ p)   = p
isSuccessF (Stage p)      = p

-- isSuccessT = foldFreeT (const $ returnM False) (returnM.isSuccessF)

annotateLevel :: forall f a. (Functor f) => Free f a -> Free (AnnotatedF Int f) a
annotateLevel = go 0 where
  go i (Pure  x) = return x
  go i (Impure x) = Impure (Annotated i $ fmap (go (succ i)) x)

-- -----------------
-- Functor instances
-- -----------------
instance Foldable ProofF where foldMap = T.foldMapDefault
$(derive makeFunctor     ''ProofF)
$(derive makeTraversable ''ProofF)
