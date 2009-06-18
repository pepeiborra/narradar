{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
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

import Narradar.Types
import Narradar.Utils
import qualified Narradar.ArgumentFiltering as AF

import Control.Monad.Free.Narradar

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
type ProblemProof  id v = ProofC (Problem id v)
type ProblemProofG id v = (MonadPlus m, MonadFree ProofF m) => m (Problem id v)
type ProblemProofC id v = ProofC (Problem id v)

success  pi p0 = wrap (Success (someInfo pi) (someProblem p0))
success' pi p0 = wrap (Success pi p0)
failP    pi p0 = wrap (Fail (someInfo pi) (someProblem p0))
failP'   pi p0 = wrap (Fail pi p0)
choiceP  p1 p2   = wrap (MPlus p1 p2)
dontKnow pi p0   = wrap (DontKnow (someInfo pi) (someProblem p0))
dontKnow' pi p0  = wrap (DontKnow pi p0)
andP pi p0 []    = success pi p0
andP pi p0 pp    = wrap (And (someInfo pi) (someProblem p0) pp)
andP' pi p0 []   = success' pi p0
andP' pi p0 pp   = wrap (And pi p0 pp)
orP  pi p0 []    = success pi p0
orP  pi p0 pp    = wrap (Or (someInfo pi) (someProblem p0) pp)
orP' pi p0 []    = success' pi p0
orP' pi p0 pp    = wrap (Or pi p0 pp)
step pi p0 p     = wrap (Step (someInfo pi) (someProblem p0) (return p))
step' pi p0 p    = wrap (Step pi p0 p)
mand p1 p2       = wrap (MAnd p1 p2)
mdone            = wrap MDone
mall             = foldr mand mdone
mplusPar p1 p2   = wrap (MPlusPar p1 p2)
msumPar          = foldr mplusPar mzero
stage            = wrap . Stage

deriving instance (Show k) => Show (ProofF k)

data SomeProblem where
    SomeProblem       :: (Ord id, Ppr id, Ord v, Ppr v) => !(Problem id v) -> SomeProblem

instance Show SomeProblem where
    show (SomeProblem p) = "<some problem>"

instance Ppr SomeProblem where
  ppr (SomeProblem p) = ppr p

someProblem :: (Ord id, Ppr id, Ord v, Ppr v) => Problem id v -> SomeProblem
someProblem p@Problem{} = SomeProblem (trimProblem p)

-- trimProblem (Problem typ trs (DPTRS dps_a _ _ _) ) = Problem typ trs (tRS$ A.elems dps_a)
-- ^^ DISABLED. The problem is that the pairs get stored in a Set and thus reordered, which breaks the representation of DP graphs later
trimProblem p = p

data SomeInfo where SomeInfo :: (Ord id, Ppr id) => !(ProcInfo id) -> SomeInfo
instance Ppr SomeInfo where ppr (SomeInfo pi) = ppr pi
instance Show SomeInfo where show = show . ppr
someInfo = SomeInfo

instance (Ord v, Ppr v, Ppr id, Ppr v) => Ppr (ProblemProofC id v) where ppr = pprProof
pprProof = foldFree (const Doc.empty) ppr -- where leaf prob = ppr prob $$ text ("RESULT: Not solved yet")


instance (Ppr a) => Ppr (ProofF a) where ppr = pprProofF
pprProofF = f where
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
      f DontKnow{..} =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo  $$
        text ("RESULT: Don't know.") $$
        proofTail procInfo
      f p@(Or proc prob sub) =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)
      f (And proc prob sub)
       | length sub > 1 =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        text ("Problem was divided in " ++ show (length sub) ++ " subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)
       | otherwise =
        ppr prob $$
        text "PROCESSOR: " <> ppr proc $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr sub)
      f (Step{..}) =
        ppr problem $$
        text "PROCESSOR: " <> ppr procInfo $$
        nest 8 (ppr subProblem)
      f p@(MPlus p1 p2) =
        text ("There is a choice.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr [p1,p2])
      f p@(MPlusPar p1 p2) =
        text ("There is a choice.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr [p1,p2])
      f p@(MAnd p1 p2) =
        text ("Problem was divided in 2 subproblems.") $$
        nest 8 (vcat $ punctuate (text "\n") $ map ppr [p1,p2])
      f MDone = text "Done"
      f (Stage p) = ppr p

      proofTail :: SomeInfo -> Doc
      proofTail (SomeInfo (External _ (find isOutputTxt -> Just (OutputTxt txt))))
                  = text ("Output: ") <> (vcat . map text . lines) txt
      proofTail _ = Doc.empty

-- ------------------
-- Monad Transformer
-- ------------------
-- we are going to need a monad transformer (for the Aprove proc)

type ProofT   m a = FreeT ProofF m a
type PPT id f m   = ProofT m (Problem id f)

liftProofT :: P.Monad m => ProofC a -> ProofT m a
liftProofT = trans

instance (Monad m, Functor ProofF) => MonadPlus (FreeT ProofF m) where
    mplus m1 m2 = FreeT $ return $ Right (MPlus m1 m2)
    mzero       = FreeT $ return $ Right MZero

-- ------------
-- * Evaluators
-- ------------

stageProof :: MonadFree ProofF m => ProofC a -> m (m a)
stageProof = foldFree (return . return) f where
  f (Stage p) = return (unstageProof p)
  f x = wrap x
  unstageProof = join

runProof :: C (Free ProofF) a -> Maybe (ProofC ())
runProof = runProof' . improve

runProof' :: (MonadFree ProofF proof) => ProofC a -> Maybe (proof b)
runProof' p = listToMaybe $ observeMany 1 search where
  -- First turn the proof, i.e. a tree of problems, into a tree of proofs.
  -- This is done by replacing stage nodes by leafs containing the staged subproof
  p'     = stageProof p
  search = do
  -- Next we define the search, which is done using eval.
  -- The search returns a mp list of (potentially) succesful proofs, i.e. tree of problems.
    sol <- foldFree return evalF p'
--  let sol' = unstageProof sol
    -- we search through these one by one
    -- WE SHOULD SORT THEM FIRST
    -- by whether they are a staged proof or not,
    -- so that we look at the easy wins first.
    -- Ultimately runProofDirect performs a good old search over every proof,
    -- regarding any remaining unsolved problem as a failure
    runProofDirect (sol `asTypeOf` p)

  runProofDirect p = foldFree (const mzero) evalF p `asTypeOf` search

runProofDFS = listToMaybe . observeMany 1 . foldFree (const mzero) evalF
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
evalF Success{..}    = return (wrap Success{..})
evalF MDone          = return (wrap MDone)
evalF (MPlus p1 p2)  = p1 `M.mplus` p2
evalF (MPlusPar p1 p2) = p1 `M.interleave` p2
evalF (And pi pb ll) = (wrap . And  pi pb) <$> P.sequence ll
evalF (Or  pi pb ll) = (wrap . Step pi pb) <$> msum ll
evalF (MAnd  p1 p2)  = p1 >>= \s1 -> p2 >>= \s2 ->
                       return (wrap $ MAnd s1 s2)
evalF (Step pi pb p) = (wrap . Step pi pb) <$> p
evalF (Stage  p) = p

sequencePar []     = return []
sequencePar (x:xx) = x >>- \x' -> (x':) `liftM` sequencePar xx

unsafeUnwrapIO :: Functor f => FreeT f IO a -> Free f a
unsafeUnwrapIO (FreeT m) = go (unsafePerformIO m) where
  go (Left  a) = return a
  go (Right f) = wrap (unsafeUnwrapIO <$> f)


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


-- -------------------
-- MonadPlus instances
-- -------------------

instance MonadPlus (Free ProofF) where
    mplus p1 p2 = wrap (MPlus p1 p2)
    mzero       = wrap MZero

instance MonadPlus (C (Free ProofF)) where
    mplus p1 p2 = wrap $ MPlus p1 p2
    mzero       = wrap MZero
