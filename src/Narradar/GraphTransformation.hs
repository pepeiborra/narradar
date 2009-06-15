{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Narradar.GraphTransformation (narrowing, instantiation, finstantiation) where

import Control.Applicative
import Control.Monad.Supply
import Control.Parallel.Strategies
import Data.Array.IArray hiding ( array )
import Data.Array.Base (numElements)
import qualified Data.Array.IArray as A
import Data.Foldable (toList, foldMap)
import qualified Data.Graph as Gr
import Data.AlaCarte.Instances
import Data.List (nub, foldl1', isPrefixOf, (\\))
import Data.Maybe
import qualified Data.Set as Set
import Control.Monad.Logic
import Text.XHtml (Html)

import Control.Monad.Free.Narradar
import Narradar.Types hiding ((//), (!))
import TRS (open, EqModulo_(..))
import Narradar.Utils ((<$$>), (.|.), snub, foldMap2, trace)
import Narradar.Proof
import Narradar.DPairs
import Narradar.UsableRules

import qualified TRS


{-# SPECIALIZE narrowing      :: MonadFree ProofF mf => ProblemG LId BasicLId -> [mf(ProblemG LId BasicLId)] #-}
{-# SPECIALIZE instantiation  :: MonadFree ProofF mf => ProblemG LId BasicLId -> [mf(ProblemG LId BasicLId)] #-}
{-# SPECIALIZE finstantiation :: MonadFree ProofF mf => ProblemG LId BasicLId -> [mf(ProblemG LId BasicLId)] #-}

--narrowing, instantiation, finstantiation :: forall f id a. (DPMark f, NFData (f(Term f)), Hole :<: f, T id :<: f, Show id, {- HasTrie (f(Term f)),-} id ~ Identifier a, Ord a) => ProblemG id f -> [ProblemProofG id f]
narrowing p@(Problem typ@(isGNarrowing .|. isBNarrowing -> True) trs dptrs@(DPTRS dpsA gr unif sig))
    = [ step (NarrowingP olddp (tRS newdps)) p (Problem typ trs (expandDPair typ trs dptrs i newdps))
                     | (i,dps') <- dpss
                     , let olddp  = tRS[dpsA !  i] `asTypeOf` trs
                     , let newdps = dps' !! i]
    where --  dpss = snd <$$> (map concat $ filter (all (not.null)) $ maps f (assocs dpsA))
          dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
          f (i, olddp@(_s :-> t))
              | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
              | otherwise = []
           where
             newdps
              | (isBNarrowing .|. isGNarrowing) typ || isLinear t
              , isNothing (unify' t `mapM` uu)
              , new_dps <- [(i,dp') | (dp',p) <- narrow1DP olddp
                                         , let validPos = Set.toList(Set.fromList(positions (runSupply(icap trs t))) `Set.intersection` pos_uu)
                                         , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs.snd) new_dps then [] else new_dps

              | otherwise = []

               where uu     = map (lhs . (dpsA !)) (gr ! i)
                     pos_uu = if null uu then Set.empty else foldl1' Set.intersection (Set.fromList . positions <$> uu)

          narrow1DP (l :-> r) = [ (l TRS.// theta :-> r', p)
                                  | ((r',p),theta) <- observeAll (narrow1P (rules trs) r)
                                  ]

narrowing p = [return p]

instantiation p@(Problem typ@(isAnyNarrowing->True) trs dptrs@(DPTRS dpsA gr unif _))
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | otherwise = [ step (InstantiationP olddp (tRS newdps)) p (Problem typ trs (expandDPair typ trs dptrs i newdps))
                     | (i,dps') <- dpss
                     , let olddp  = tRS[dpsA ! i] `asTypeOf` trs
                     , let newdps = dps' !! i ]

   where dps  = elems dpsA `const` unif
         dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
         f  (i,olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
            where newdps = [ (i, s TRS.// sigma :-> t TRS.// sigma)
                           | Just sigma <- [dpUnify dptrs i m | (m,n) <- Gr.edges gr, n == i]]

instantiation p = [return p]

finstantiation p@(Problem typ@(isAnyNarrowing ->True) trs dptrs@(DPTRS dpsA gr unif sig))
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | otherwise = [ step (FInstantiationP olddp (tRS newdps)) p (Problem typ trs (expandDPair typ trs dptrs i newdps))
                     | (i, dps') <- dpss
                     , let olddp  = tRS[dpsA !  i] `asTypeOf` trs
                     , let newdps = dps' !! i]
   where dps  = elems dpsA
         dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
         f (i, olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
              where newdps = [(i,  s TRS.// sigma :-> t TRS.// sigma)
                             | Just sigma <- [dpUnify dptrs j i | j <- gr ! i]]
finstantiation p = [return p]

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
propMaps f xx = maps f xx == maps' f xx where types = (xx :: [Bool], f :: Bool -> [Bool])

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
