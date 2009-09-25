{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module Narradar.Processor.GraphTransformation where

import Control.Applicative
import Control.Monad.Identity (Identity(..))
import Control.Monad.Logic
import Data.Array.IArray hiding ( array )
import qualified Data.Array.IArray as A
import qualified Data.Graph as Gr
import Data.List (foldl1', isPrefixOf, nub)
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Text.XHtml (HTML)

import Narradar.Types hiding ((!))
import Narradar.Types.TRS
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Utils

import Data.Term.Narrowing


data NarrowingP     = NarrowingP
data Instantiation  = Instantiation
data FInstantiation = FInstantiation

-- Narrowing

instance ( Ord (Term t Var), Pretty (Term t Var), Unify t, HasId t, TermId t ~ Identifier id
         , Info info GraphTransformationProof
         ) =>
    Processor info NarrowingP (NarradarProblem Rewriting t) (NarradarProblem Rewriting t) where
  applySearch NarrowingP = narrowing

instance (Ord (Term t Var), Pretty (Term t Var), Unify t, HasId t, TermId t ~ Identifier id
         , Info info GraphTransformationProof
         ) =>
    Processor info NarrowingP (NarradarProblem Narrowing t) (NarradarProblem Narrowing t) where
  applySearch NarrowingP = narrowing

instance (Ord (Term t Var), Pretty (Term t Var), Unify t, HasId t, TermId t ~ Identifier id
         , Info info GraphTransformationProof
         ) =>
    Processor info NarrowingP (NarradarProblem IRewriting t) (NarradarProblem IRewriting t) where
  applySearch NarrowingP = narrowing_innermost

instance (Ord (Term t Var), Pretty (Term t Var), Unify t, HasId t, TermId t ~ Identifier id
         , Info info GraphTransformationProof
         ) =>
    Processor info NarrowingP (NarradarProblem CNarrowing t) (NarradarProblem CNarrowing t) where
  applySearch NarrowingP = narrowing_innermost

-- Instantiation

instance (trs ~ NarradarTRS t v
         ,v   ~ Var
         ,Identifier id ~ TermId t, HasId t
         ,Unify t, Pretty (Term t Var), Pretty typ, Ord (Term t Var)
         ,IsDPProblem typ, Traversable (DPProblem typ)
         ,IUsableRules t v (typ, trs), ICap t v (typ, trs)
         ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ, [Rule t v])
         ,Info info GraphTransformationProof
         ) =>
    Processor info Instantiation (NarradarProblem typ t) (NarradarProblem typ t) where
  applySearch Instantiation = instantiation


-- Forward Instantiation

instance (trs ~ NarradarTRS t v
         ,v   ~ Var
         ,Identifier id ~ TermId t, HasId t
         ,Unify t, Pretty (Term t Var), Pretty typ, Ord (Term t Var)
         ,IsDPProblem typ, Traversable (DPProblem typ)
         ,IUsableRules t v (typ, trs), ICap t v (typ, trs)
         ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ, [Rule t v])
         ,Info info GraphTransformationProof
         ) =>
    Processor info FInstantiation (NarradarProblem typ t) (NarradarProblem typ t) where
  applySearch FInstantiation = finstantiation


-- -------
-- Proofs
-- -------

data GraphTransformationProof where
    NarrowingProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> [Rule t v]          -- ^ New pairs
                   -> GraphTransformationProof
    InstantiationProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> [Rule t v]          -- ^ New pairs
                   -> GraphTransformationProof
    FInstantiationProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> [Rule t v]          -- ^ New pairs
                   -> GraphTransformationProof

instance Pretty GraphTransformationProof where
  pPrint (NarrowingProof old new) =
                                 text "Narrowing Processor." <+>
                                 text "Pair" <+> pPrint old <+> text "replaced by" <+> pPrint new

  pPrint (InstantiationProof old new) =
                                 text "Instantiation Processor." <+>
                                 text "Pair" <+> pPrint old <+> text "replaced by" <+> pPrint new

  pPrint (FInstantiationProof old new) =
                                 text "FInstantiation Processor." <+>
                                 text "Pair" <+> pPrint old <+> text "replaced by" <+> pPrint new

-- ----------------
-- Implementation
-- ----------------
-- Narrowing

narrowing, narrowing_innermost
          :: (p  ~ DPProblem typ trs
             ,trs ~ NarradarTRS t v
             ,TermId t  ~ Identifier id, HasId t, Unify t
             ,Enum v, GetVars v v, Ord (Term t v)
             ,IsDPProblem typ, Traversable (DPProblem typ)
             ,IUsableRules t v (typ, trs), ICap t v (typ,trs)
             ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ,[Rule t v])
             ,Pretty (Term t v), Pretty v, Pretty typ
             ,Info info p
             ,Info info GraphTransformationProof
             ,Monad mp
             ) =>
             DPProblem typ trs -> [Proof info mp (DPProblem typ trs)]

narrowing p0
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise  = [ singleP (NarrowingProof olddp newdps) p0 (expandDPair p0 i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = dpsA ! i
                     , let newdps = dps' !! i]
    where --  dpss = snd <$$> (map concat $ filter (all (not.null)) $ maps f (assocs dpsA))
          (dpsA, gr) = (rulesArray (getP p0), rulesGraph (getP p0))
          dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                          , all (not.null) dps]
          f (i, olddp@(_s :-> t))
              | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
              | otherwise = []
           where
             newdps
              |  isLinear t
              , isNothing (unify' (getVariant t uu) `mapM` uu)
              , new_dps <- [(i,dp')
                              | (dp',p) <- narrow1DP (rules $ getR p0) olddp
                              , let validPos
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0)))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs.snd) new_dps then [] else new_dps

              | otherwise = []
               where uu     = map (lhs . (dpsA !)) (gr ! i)
                     pos_uu = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)

narrowing_innermost p0
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (NarrowingProof olddp newdps) p0 (expandDPair p0 i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = dpsA ! i
                     , let newdps = dps' !! i]
    where --  dpss = snd <$$> (map concat $ filter (all (not.null)) $ maps f (assocs dpsA))
          (dpsA, gr) = (rulesArray (getP p0), rulesGraph (getP p0))
          dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                          , all (not.null) dps]
          f (i, olddp@(_s :-> t))
              | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
              | otherwise = []
           where
             newdps
              | isNothing (unify' (getVariant t uu) `mapM` uu)
              , new_dps <- [(i,dp')
                              | (dp',p) <- narrow1DP (rules $ getR p0) olddp
                              , let validPos
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0)))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs.snd) new_dps then [] else new_dps

              | otherwise = []
               where uu     = map (lhs . (dpsA !)) (gr ! i)
                     pos_uu = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)

narrow1DP rr (l :-> r) = [ (applySubst theta l :-> r', p)
                           | ((r',p),theta) <- observeAll (narrow1P rr r) ]

-- Instantiation

instantiation, finstantiation
          :: forall typ trs mp t v p id info.
             (p  ~ DPProblem typ trs, Info info p
             ,trs ~ NarradarTRS t v
             ,TermId t ~ Identifier id, HasId t, Unify t
             ,Enum v, GetVars v v
             ,IsDPProblem typ, Traversable (DPProblem typ)
             ,Pretty (Term t v), Ord(Term t v), Pretty v, Pretty typ
             ,IUsableRules t v (typ, trs), ICap t v (typ, trs)
             ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ, [Rule t v])
             ,Info info GraphTransformationProof
             ,Monad mp
             ) =>
             DPProblem typ trs -> [Proof info mp (DPProblem typ trs)]

instantiation p
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | not $ isDPTRS (getP p) = error "instantiationProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (InstantiationProof olddp newdps) p (expandDPair p i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = dpsA  ! i
                     , let newdps = dps' !! i ]

   where (dpsA, gr) = (rulesArray (getP p), rulesGraph (getP p))
         dps  = elems dpsA
         dpss = [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                    , all (not.null) dps]
         f :: (Int, Rule t v) -> [(Int, Rule t v)]
         f  (i,olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
            where newdps = [ (i, applySubst sigma s :-> applySubst sigma t)
                            | Just sigma <- snub [dpUnify (getP p) i m | (m,n) <- Gr.edges gr, n == i]]

--instantiation p = [return p]

-- Forward instantiation

finstantiation p
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | not $ isDPTRS (getP p) = error "finstantiationProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (FInstantiationProof olddp newdps) p
                           (expandDPair p i newdps)
                     | (i, dps') <- dpss
                     , let olddp  = dpsA !  i
                     , let newdps = dps' !! i]
   where (dpsA, gr) = (rulesArray (getP p), rulesGraph (getP p))
         dps  = elems dpsA
         dpss = [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                    , all (not.null) dps]
         f :: (Int, Rule t v) -> [(Int, Rule t v)]
         f (i, olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
              where newdps = [(i, applySubst sigma s :-> applySubst sigma t)
                             | Just sigma <- snub [dpUnifyInv (getP p) j i | j <- gr ! i]]
-- finstantiation p = [return p]


-- I should teach myself about comonads
-- http://sigfpe.blogspot.com/2008/03/comonadic-arrays.html
-- ---------------------------------------------------------

maps, maps' :: Monad m => (a -> m a) -> [a] -> [[m a]]
maps f xx = concat $ elems $ array (Pointer 1 (listArray (1, length xx) xx) =>> appF) where
    appF (Pointer i a) = let a' = amap return a in  map elems [a' // [(i, f(a!i))] ]

maps' f xx = [ updateAt i xx | i <- [0..length xx - 1]] where
  updateAt 0 (x:rest) = f x      : map return rest
  updateAt i (x:xx)   = return x : updateAt (i-1) xx

-- maps and maps' are equivalent
propMaps f xx = maps f xx == maps' f xx where _types = (xx :: [Bool], f :: Bool -> [Bool])

-- ------------------------------
-- Extracted from category-extras
-- ------------------------------
data Pointer i a = Pointer { index :: i, array :: Array i a } deriving (Show,Read)

instance Ix i => Functor (Pointer i) where
    fmap f (Pointer i a) = Pointer i (fmap f a)

instance Ix i => Copointed (Pointer i) where
    extract (Pointer i a) = a ! i

instance Ix i => Comonad (Pointer i) where
    extend f (Pointer i a) = Pointer i . listArray bds $ fmap (f . flip Pointer a) (range bds) where
                                     bds = bounds a


class Copointed w => Comonad w where
        duplicate :: w a -> w (w a)
        extend :: (w a -> b) -> w a -> w b
        extend f = fmap f . duplicate
        duplicate = extend id

-- | 'extend' with the arguments swapped. Dual to '>>=' for monads.
(=>>) :: Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

class Functor f => Copointed f where
        extract :: f a -> a -- Algebra f a

instance Copointed Identity where
        extract = runIdentity

instance Copointed ((,)e) where
    extract = snd
