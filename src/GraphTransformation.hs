{-# LANGUAGE PatternGuards, ViewPatterns, ScopedTypeVariables, FlexibleContexts #-}

module GraphTransformation where

import Control.Applicative
import Data.Foldable (toList)
import Data.List (nub)
import Data.Maybe
import Data.Array.IArray hiding ( array )
import Control.Comonad.Pointer
import Control.Monad.Logic
import Text.XHtml (Html)

import Types hiding ((//), (!))
import TRS (open)
import Utils ((<$$>))
import Proof
import DPairs

import qualified TRS

narrowing, instantiation, finstantiation :: (Hole :<: f) => Problem f -> ProblemProof Html f
narrowing p@(Problem typ@(isAnyNarrowing->True) trs (TRS (toList -> dps) sig))
  | null dpss || [[]] == dpss = dontKnow NarrowingP p
  | otherwise = orP NarrowingP p [return $ Problem typ trs (tRS newdps sig) | newdps <- dpss]
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

instantiation p@(Problem typ@(isAnyNarrowing->True) trs (TRS (toList -> dps) sig))
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | null dpss || dpss == [dps] = dontKnow InstantiationP p
  | otherwise = orP InstantiationP p [return $ Problem typ trs (tRS newdps sig)
                                          | newdps <- dpss]
   where dpss = nub (snd <$$> (catMaybes $ sequence <$>
                              maps (uncurry f) (zip dps (tail dps ++ dps))))
         f  (u :-> v) (s :-> t) = listToMaybe
                                  [(s :-> t, s TRS.// sigma :-> t TRS.// sigma)
                                      | let [v'] = variant' [ren$ cap trs v] [s],
                                        sigma <- v' `unify` s]

instantiation p = return p

finstantiation p@(Problem typ@(isAnyNarrowing->True) trs (TRS (toList -> dps) sig))
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | null dpss || dpss == [dps] = dontKnow FInstantiationP p
  | otherwise = orP FInstantiationP p [return $ Problem typ trs (tRS newdps sig)
                                          | newdps <- dpss]
   where dpss = nub (fst <$$> (catMaybes $ sequence <$>
                              maps (uncurry f) (zip dps (tail dps ++ dps))))
         f (s :-> t) (v:->w) = listToMaybe
                                  [(s TRS.// sigma :-> t TRS.// sigma, s :-> t)
                                      | let [v'] = variant' [ren$ capInv trs v] [t],
                                        sigma <- v' `unify` t]

finstantiation p = return p

capInv trs@TRS{} t
       | collapsing trs = var 0
       | Just (T (s::Identifier) tt) <- open t
       = term s [if isDefined (swapRule <$> rules trs) t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
       | otherwise = t

collapsing trs@TRS{} = any (isVar.rhs) (rules trs)