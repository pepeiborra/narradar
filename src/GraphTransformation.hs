{-# LANGUAGE PatternGuards, FlexibleContexts #-}

module GraphTransformation where

import Data.Maybe (isNothing)
import Data.Array.IArray hiding ( array )
import Control.Comonad.Pointer
import Control.Monad.Logic
import Text.XHtml (Html)

import Types hiding ((//), (!))
import Problem
--import NarrowingProblem
import DPairs

import qualified TRS

narrowingProcessor :: (Hole :<: f) => Problem f -> ProblemProgress Html f
narrowingProcessor p@(Problem Narrowing trs (TRS dps sig))
  | null dpss || [[]] == dpss = dontKnow NarrowingP p
  | otherwise = orP NarrowingP p [return $ Problem Narrowing trs (TRS newdps sig) | newdps <- dpss]
    where dpss = fst <$$> map concat (filter (all (not.null)) (maps (uncurry f) (zip dps (tail dps ++ dps))))
          f dp@(_ :-> r) nxt@(l :-> _)
              | isLinear r, isNothing (r `unify` l) = [(dp', nxt) | dp' <- narrow1DP dp]
              | otherwise                           = []
          narrow1DP (l :-> r) = [(l TRS.// theta) :-> markDP r'| (r',theta) <- observeAll (narrow1 (rules trs) (unmarkDP r))]
          (<$$>) = map . map

-- I should teach myself about comonads
-- http://sigfpe.blogspot.com/2008/03/comonadic-arrays.html
maps f xx = concat $ elems $ array (Pointer 1 (listArray (1, length xx) xx) =>> appF) where
    appF  = \(Pointer i a) -> let a' = amap (:[]) a in map elems [a' // [(i, f(a!i))] ]