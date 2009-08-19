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
import Data.List (foldl1', isPrefixOf)
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Text.XHtml (HTML)

import Narradar.Types hiding ((!))
import Narradar.Types.TRS
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Utils

import Data.Term.Narrowing


data NarrowingP     = NarrowingP
data Instantiation  = Instantiation
data FInstantiation = FInstantiation

-- Narrowing

instance (Ppr (Identifier id), Ppr id, Ord id) =>
    Processor NarrowingP (NarradarTRS (Identifier id) Var) Rewriting Rewriting where
  applySearch NarrowingP = narrowing

instance (Ppr (Identifier id), Ppr id, Ord id) =>
    Processor NarrowingP (NarradarTRS (Identifier id) Var) Narrowing Narrowing where
  applySearch NarrowingP = narrowing

instance (Ppr (Identifier id), Ppr id, Ord id) =>
    Processor NarrowingP (NarradarTRS (Identifier id) Var) IRewriting IRewriting where
  applySearch NarrowingP = narrowing_innermost
instance (Ppr (Identifier id), Ppr id, Ord id) =>
    Processor NarrowingP (NarradarTRS (Identifier id) Var) CNarrowing CNarrowing where
  applySearch NarrowingP = narrowing_innermost

-- Instantiation

instance (trs ~ NarradarTRS (Identifier id) v
         ,t   ~ TermF (Identifier id)
         ,v   ~ Var
         ,IsDPProblem typ, Traversable (DPProblem typ), ProblemInfo (DPProblem typ trs)
         ,IUsableRules t v (typ, trs), ICap t v (typ, trs)
         ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ, [Rule t v])
         ,Ppr (Identifier id), Ppr id, Ord id
         ) =>
    Processor Instantiation (NarradarTRS (Identifier id) Var) typ typ where
  applySearch Instantiation = instantiation


-- Forward Instantiation

instance (trs ~ NarradarTRS (Identifier id) v
         ,t   ~ TermF (Identifier id)
         ,v   ~ Var
         ,IsDPProblem typ, Traversable (DPProblem typ), ProblemInfo (DPProblem typ trs)
         ,IUsableRules t v (typ, trs), ICap t v (typ, trs)
         ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ, [Rule t v])
         ,Ppr (Identifier id), Ppr id, Ord id
         ) =>
    Processor FInstantiation (NarradarTRS (Identifier id) Var) typ typ where
  applySearch FInstantiation = finstantiation


-- -------
-- Proofs
-- -------
data NarrowingProof where NarrowingProof :: Ppr (Rule t v) =>  Rule t v   -- ^ Old pair
                                                           -> [Rule t v]  -- ^ New pairs
                                                           -> NarrowingProof

instance ProofInfo NarrowingProof
instance Ppr NarrowingProof where
  ppr (NarrowingProof old new) = text "Narrowing Processor." <+>
                                 text "Pair" <+> ppr old <+> text "replaced by" <+> ppr new

data InstantiationProof where InstantiationProof :: Ppr (Rule t v) =>  Rule t v   -- ^ Old pair
                                                           -> [Rule t v]  -- ^ New pairs
                                                           -> InstantiationProof

instance ProofInfo InstantiationProof
instance Ppr InstantiationProof where
  ppr (InstantiationProof old new) = text "Instantiation Processor." <+>
                                 text "Pair" <+> ppr old <+> text "replaced by" <+> ppr new

data FInstantiationProof where FInstantiationProof :: Ppr (Rule t v) =>  Rule t v   -- ^ Old pair
                                                           -> [Rule t v]  -- ^ New pairs
                                                           -> FInstantiationProof

instance ProofInfo FInstantiationProof
instance Ppr FInstantiationProof where
  ppr (FInstantiationProof old new) = text "FInstantiation Processor." <+>
                                 text "Pair" <+> ppr old <+> text "replaced by" <+> ppr new

-- ----------------
-- Implementation
-- ----------------
-- Narrowing

narrowing, narrowing_innermost
          :: (p  ~ NarradarProblem typ (Identifier id)
             ,t  ~ TermF (Identifier id)
             ,v  ~ Var, Enum v
             ,trs ~ NarradarTRS (Identifier id) v
             ,IsDPProblem typ, Traversable (DPProblem typ), ProblemInfo p
             , Ppr (Identifier id), Ppr id, Ord id, HTML p, Ppr p
             ,IUsableRules t v (typ, trs), ICap t v (typ,trs)
             ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ,[Rule t v])
             ) =>
             NarradarProblem typ (Identifier id) -> [Proof (NarradarProblem typ (Identifier id))]

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
          :: (p  ~ NarradarProblem typ (Identifier id), ProblemInfo p
             ,t  ~ TermF (Identifier id)
             ,v  ~ Var, Enum v
             ,trs ~ NarradarTRS (Identifier id) v
             ,IsDPProblem typ, Traversable (DPProblem typ)
             , Ppr (Identifier id), Ppr id, Ord id, HTML p, Ppr p
             ,IUsableRules t v (typ, trs), ICap t v (typ, trs)
             ,IUsableRules t v (typ, [Rule t v]), ICap t v (typ, [Rule t v])
             ) =>
             NarradarProblem typ (Identifier id) -> [Proof (NarradarProblem typ (Identifier id))]

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
