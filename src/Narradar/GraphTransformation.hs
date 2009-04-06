{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}

module Narradar.GraphTransformation (narrowing, instantiation, finstantiation) where

import Control.Applicative
import Data.Array.IArray hiding ( array )
import Data.Array.Base (numElements)
import qualified Data.Array.IArray as A
import Data.Foldable (toList, foldMap)
import qualified Data.Graph as Gr
import Data.List (nub, foldl1', isPrefixOf, (\\))
import Data.Maybe
import qualified Data.Set as Set
import Control.Comonad.Pointer
import Control.Monad.Logic
import Text.XHtml (Html)

import Narradar.Types hiding ((//), (!))
import TRS (open, EqModulo_(..))
import Narradar.Utils ((<$$>), (.|.), snub, foldMap2, trace)
import Narradar.Proof
import Narradar.DPairs
import Narradar.UsableRules

import qualified TRS


{-# SPECIALIZE narrowing      :: ProblemG LId BasicLId -> [ProblemProofG LId Html BasicLId] #-}
{-# SPECIALIZE instantiation  :: ProblemG LId BasicLId -> [ProblemProofG LId Html BasicLId] #-}
{-# SPECIALIZE finstantiation :: ProblemG LId BasicLId -> [ProblemProofG LId Html BasicLId] #-}

narrowing, instantiation, finstantiation :: forall f id a. (DPMark f, NFData (f(Term f)), Hole :<: f, T id :<: f, Show id, {- HasTrie (f(Term f)),-} id ~ Identifier a, Ord a) => ProblemG id f -> [ProblemProofG id Html f]
narrowing p@(Problem typ@(isGNarrowing .|. isBNarrowing -> True) trs (DPTRS dpsA gr unif sig))
    = [ step (NarrowingP olddp (tRS newdps)) p (expandDPair p i newdps)
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
                                         , let validPos = Set.toList(Set.fromList(positions (icap trs t)) `Set.intersection` pos_uu)
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

instantiation p@(Problem typ@(isAnyNarrowing->True) trs dptrs@(DPTRS dpsA gr _ _))
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | otherwise = [ step (InstantiationP olddp (tRS newdps)) p (expandDPair p i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = tRS[dpsA ! i] `asTypeOf` trs
                     , let newdps = dps' !! i ]

   where dps  = elems dpsA
         dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
         f  (i,olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
            where newdps = [ (i, s TRS.// sigma :-> t TRS.// sigma)
                           | Just sigma <- [dpUnify dptrs m i | (m,n) <- Gr.edges gr, n == i]]

instantiation p = [return p]

finstantiation p@(Problem typ@(isAnyNarrowing ->True) trs dptrs@(DPTRS dpsA gr unif sig))
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | otherwise = [ step (FInstantiationP olddp (tRS newdps)) p (expandDPair p i newdps)
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
                                      | Just sigma <- [dpUnify dptrs i j | j <- gr ! i]]
finstantiation p = [return p]

--expandDPair :: ProblemG id f -> Int -> [DP f] -> ProblemG id f
--expandDPair (Problem typ rules (DPTRS dps gr unif sig)) i newdps | trace ("expandDPair i="++ show i ++ " dps=" ++ show(numElements dps) ++ " newdps=" ++ show (length newdps)) False = undefined
expandDPair (Problem typ rules (DPTRS dps gr (unif, unifInv) sig)) i newdps = Problem typ rules dptrs'
  where
    dptrs' = DPTRS a_dps' gr (mkUnif' unif unif_new, mkUnif' unifInv unifInv_new) sig -- (getSignature dps')
    a_dps' = A.listArray (0,length dps' - 1) dps'
    dps'   = dps1 ++  dps2 ++ refreshRules ids newdps
    (dps1,_:dps2) = splitAt i (elems dps)
    mkUnif' arr arr' =
       A.array ((0,0), (length dps' - 1, length dps' - 1))
                       ([((x',y'), sigma) | ((x,y), sigma) <- assocs arr
                                          , x /= i, y /= i
                                          , let x' = if x < i then x else x-1
                                          , let y' = if y < i then y else y-1] ++
                        concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
--                                 [ (in1, computeDPUnifier typ rules a_dps' in1)
--                                 , (in2, computeDPUnifier typ rules a_dps' in2)]
                                 | j <- [0..length newdps -1], k <- [0..length dps'-1]
                                 , let in1 = (c0+j,k), let in2 = (k,c0+j)])
                      where (_,c0) = bounds dps
    ids = [0..] \\ [ i | v <- foldMap2 vars' dps, let Just i = uniqueId v]
    (unif_new, unifInv_new) = computeDPUnifiers typ rules dps'
    isArray :: Array i e -> Array i e
    isArray = id

expandDPair (Problem typ trs dps@TRS{}) i newdps = Problem typ trs (tRS dps' `asTypeOf` dps) where
    dps'          = dps1 ++ dps' ++ dps2
    (dps1,_:dps2) = splitAt i (rules dps)

-- I should teach myself about comonads
-- http://sigfpe.blogspot.com/2008/03/comonadic-arrays.html
maps, maps' :: Monad m => (a -> m a) -> [a] -> [[m a]]
maps f xx = concat $ elems $ array (Pointer 1 (listArray (1, length xx) xx) =>> appF) where
    appF (Pointer i a) = let a' = amap return a in  map elems [a' // [(i, f(a!i))] ]

maps' f xx = [ updateAt i xx | i <- [0..length xx - 1]] where
  updateAt 0 (x:rest) = f x      : map return rest
  updateAt i (x:xx)   = return x : updateAt (i-1) xx

-- maps and maps' are equivalent
propMaps f xx = maps f xx == maps' f xx where types = (xx :: [Bool], f :: Bool -> [Bool])
