{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.GraphTransformation (narrowing, instantiation, finstantiation) where

import Control.Applicative
import Data.Foldable (toList)
import Data.List (nub)
import Data.Maybe
import Data.Array.IArray hiding ( array )
import Control.Comonad.Pointer
import Control.Monad.Logic
import Text.XHtml (Html)

import Narradar.Types hiding ((//), (!))
import TRS (open)
import Narradar.Utils ((<$$>), (.|.))
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

narrowing, instantiation, finstantiation :: forall f id a. (DPMark f, Hole :<: f, T id :<: f, Show id, id ~ Identifier a) => ProblemG id f -> ProblemProofG id Html f
narrowing p@(Problem typ@(isGNarrowing .|. isBNarrowing -> True) trs (TRS (toList -> dps) sig))
  | null dpss || [[]] == dpss = dontKnow NarrowingP p
  | otherwise = orP NarrowingP p [return $ Problem typ trs (tRS' newdps sig) | newdps <- dpss]
    where dpss = fst <$$> (map concat $ filter (all (not.null)) $
                      maps (uncurry f) (zip dps (tail dps ++ dps)))
          f dp@(_ :-> r) nxt@(l :-> _)
              | isNothing (r `unify` l) =
                  let new_dps = [(dp', nxt) | (dp',p) <- narrow1DP dp]
                  in -- extra condition to avoid specializing to pairs whose rhs are variables
                      -- (I don't recall having seen this in any paper but surely is common knowledge)
                    if any (isVar.rhs.fst) new_dps then [] else new_dps
              | otherwise                           = []
          narrow1DP (l :-> r) = [ (l TRS.// theta :-> markDP r', p)
                                  | p <- positions (icap trs r)
                                  , ((r',p'),theta) <- observeAll (narrow1P (rules trs) (unmarkDP r))
                                  , p' == p]

narrowing p@(Problem typ@(isAnyNarrowing->True) trs (TRS (toList -> dps) sig))
  | null dpss || [[]] == dpss = dontKnow NarrowingP p
  | otherwise = orP NarrowingP p [return $ Problem typ trs (tRS' newdps sig) | newdps <- dpss]
    where dpss = fst <$$> (map concat $ filter (all (not.null)) $
                      maps (uncurry f) (zip dps (tail dps ++ dps)))
          f dp@(_ :-> r) nxt@(l :-> _)
              | isLinear r, isNothing (r `unify` l) =
                  let new_dps = [(dp', nxt) | dp' <- narrow1DP dp]
                  in -- extra condition to avoid specializing to pairs whose rhs are variables
                      -- (I don't recall having seen this in any paper but surely is common knowledge)
                    if any (isVar.rhs.fst) new_dps then [] else new_dps
              | otherwise                           = []
          narrow1DP (l :-> r) = [ l TRS.// theta :-> markDP r'
                                  | (r',theta) <- observeAll (narrow1 (rules trs) (unmarkDP r))]

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

instantiation p@(Problem typ@(isBNarrowing .|. isGNarrowing -> True) trs (TRS (toList -> dps) sig))
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | null dpss = error "Instantiation: weird..."
  | dpss == [dps] = dontKnow InstantiationP p
  | otherwise = orP InstantiationP p [return $ Problem typ trs (tRS' newdps sig)
                                          | newdps <- dpss]
   where dpss = nub (catMaybes $ sequence <$> maps f dps)
         f  (s :-> t) = listToMaybe
                                  [(s TRS.// sigma :-> t TRS.// sigma)
                                      | v :-> w <- dps,
                                        let [w'] = variant' [icap trs w] [s],
                                        sigma <- w' `unify` s]

instantiation p@(Problem typ@(isAnyNarrowing->True) trs (TRS (toList -> dps) sig))
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | null dpss = error "Instantiation: weird..."
  | dpss == [dps] = dontKnow InstantiationP p
  | otherwise = orP InstantiationP p [return $ Problem typ trs (tRS' newdps sig)
                                          | newdps <- dpss]
   where dpss = nub (catMaybes $ sequence <$> maps f dps)
         f  (s :-> t) = listToMaybe
                                  [(s TRS.// sigma :-> t TRS.// sigma)
                                      | v :-> w <- dps,
                                        let [w'] = variant' [ren$ icap trs w] [s],
                                        sigma <- w' `unify` s]

instantiation p = return p

finstantiation p@(Problem typ@(isGNarrowing .|. isBNarrowing ->True) trs (TRS (toList -> dps) sig))
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | dpss == [dps] = dontKnow FInstantiationP p
  | otherwise = orP FInstantiationP p [return $ Problem typ trs (tRS' newdps sig)
                                          | newdps <- dpss]
   where dpss = nub (catMaybes $ sequence <$> maps f dps)
         f (s :-> t) = listToMaybe
                       [(s TRS.// sigma :-> t TRS.// sigma)
                                      | v :-> w <- dps
                                      , let trs' = tRS (iUsableRules (tRS (swapRule <$> rules trs) `asTypeOf` trs) Nothing [t]) `asTypeOf` trs
                                      , let [v'] = variant' [ren$ icap trs' v] [t]
                                      , sigma <- v' `unify` t]


finstantiation p@(Problem typ@(isAnyNarrowing->True) trs (TRS (toList -> dps) sig))
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | dpss == [dps] = dontKnow FInstantiationP p
  | otherwise = orP FInstantiationP p [return $ Problem typ trs (tRS' newdps sig)
                                          | newdps <- dpss]
   where dpss = nub (catMaybes $ sequence <$> maps f dps)
         f (s :-> t) = listToMaybe
                       [(s TRS.// sigma :-> t TRS.// sigma)
                                      | v :-> w <- dps
                                      , let trs' = tRS (swapRule <$> rules trs) `asTypeOf` trs
                                      , let [v'] = variant' [ren$ icap trs' v] [t]
                                      , sigma <- v' `unify` t]

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