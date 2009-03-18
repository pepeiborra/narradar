{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.GraphTransformation (narrowing, instantiation, finstantiation) where

import Control.Applicative
import Data.Array.IArray hiding ( array )
import Data.Foldable (toList)
import qualified Data.Graph as Gr
import Data.List (nub, foldl1', isPrefixOf)
import Data.Maybe
import qualified Data.Set as Set
import Control.Comonad.Pointer
import Control.Monad.Logic
import Text.XHtml (Html)

import Narradar.Types hiding ((//), (!))
import TRS (open, EqModulo_(..))
import Narradar.Utils ((<$$>), (.|.), snub)
import Narradar.Proof
import Narradar.DPairs
import Narradar.UsableRules

import qualified TRS

{-# SPECIALIZE narrowing      :: Problem BBasicId       -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE narrowing      :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
{-# SPECIALIZE instantiation  :: Problem BBasicId       -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE instantiation  :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
{-# SPECIALIZE finstantiation :: Problem BBasicId       -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE finstantiation :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}

narrowing, instantiation, finstantiation :: forall f id a. (DPMark f, Hole :<: f, T id :<: f, Show id, id ~ Identifier a, Ord a) => ProblemG id f -> ProblemProofG id Html f
narrowing p@(Problem typ@(isGNarrowing .|. isBNarrowing -> True) trs (DPTRS dpsA gr sig))
   = msum [ step (NarrowingP olddp newdps) p (Problem typ trs (tRS' (concat dps') sig))
                     | (i,dps') <- dpss
                     , let olddp  = mkTRS[dpsA !  i] `asTypeOf` trs
                     , let newdps = mkTRS(dps' !! i) `asTypeOf` trs]
    where --  dpss = snd <$$> (map concat $ filter (all (not.null)) $ maps f (assocs dpsA))
          dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
          f (i, olddp@(_s :-> t))
              | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
              | otherwise = []
           where
             newdps
              | (isBNarrowing .|. isGNarrowing) typ || isLinear t , isNothing (unify t `mapM` uu) =
                  let new_dps = [(i,dp') | (dp',p) <- narrow1DP olddp
                                         , let validPos = Set.toList(Set.fromList(positions (icap trs t)) `Set.intersection` pos_uu)
                                         , any (`isPrefixOf` p) validPos]
                  in -- extra condition to avoid specializing to pairs whose rhs are variables
                      -- (I don't recall having seen this in any paper but surely is common knowledge)
                    if any (isVar.rhs.snd) new_dps then [] else new_dps
              | otherwise = []
               where uu     = map (lhs . (dpsA !)) (gr ! i)
                     pos_uu = if null uu then Set.empty else foldl1' Set.intersection (Set.fromList . positions <$> uu)

          narrow1DP (l :-> r) = [ (l TRS.// theta :-> r', p)
                                  | ((r',p),theta) <- observeAll (narrow1P (rules trs) r)
                                  ]

narrowing p = return p

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


instantiation p@(Problem typ@(isAnyNarrowing->True) trs (DPTRS dpsA gr sig))
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | otherwise = msum [ step (InstantiationP olddp newdps) p (Problem typ trs (tRS' (concat dps') sig))
                     | (i,dps') <- dpss
                     , let olddp  = mkTRS[dpsA !  i] `asTypeOf` trs
                     , let newdps = mkTRS(dps' !! i) `asTypeOf` trs]

   where dps  = elems dpsA
         dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
         f  (i,olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
            where newdps = [(i, s TRS.// sigma :-> t TRS.// sigma)
                                      | v :-> w <- (dpsA !) <$> [ m | (m,n) <- Gr.edges gr, n == i]
                                      , let [w'] = variant' [mbren$ icap trs w] [s]
                                      , sigma <- w' `unify` s]
         mbren = if (isBNarrowing .|. isGNarrowing) typ then id else ren

instantiation p = return p

finstantiation p@(Problem typ@(isAnyNarrowing ->True) trs (DPTRS dpsA gr sig))
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | otherwise = msum [ step (FInstantiationP olddp newdps) p (Problem typ trs (tRS' (concat dps') sig))
                     | (i, dps') <- dpss
                     , let olddp  = mkTRS[dpsA !  i] `asTypeOf` trs
                     , let newdps = mkTRS(dps' !! i) `asTypeOf` trs]
   where dps  = elems dpsA
         dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                         , all (not.null) dps]
         f (i, olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
              where newdps = [(i,  s TRS.// sigma :-> t TRS.// sigma)
                                      | v :-> w <- (dpsA !) <$> gr ! i
                                      , let trs' = tRS (swapRule <$> mbUsableRules trs t) `asTypeOf` trs
                                      , let [v'] = variant' [ren$ icap trs' v] [t]
                                      , sigma <- v' `unify` t]
         mbUsableRules trs t = if isBNarrowing typ || isGNarrowing typ
                                 then iUsableRules trs Nothing [t]
                                 else rules trs
finstantiation p = return p

capInv :: forall id f. (Ord id, T id :<: f, TRSC f) => NarradarTRS id f -> Term f -> Term f
capInv trs t
       | collapsing trs = var 0
       | Just (T (s::id) tt) <- open t
       = term s [if isDefined trs' t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
       | otherwise = t
  where trs' = tRS (swapRule <$> rules trs) :: NarradarTRS id f

collapsing trs = any (isVar.rhs) (rules trs)