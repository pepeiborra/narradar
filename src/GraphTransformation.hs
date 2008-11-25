{-# LANGUAGE FlexibleContexts #-}

module GraphTransformation where

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
  | null dpss = DontKnow{problem=p, procInfo=NarrowingP}
  | otherwise = Or NarrowingP p [NotDone $ Problem Narrowing trs (TRS newdps sig) | newdps <- dpss]
    where dpss = maps narrow1DP (filter (isLinear.rhs) dps)
          narrow1DP (l :-> r) = [(l TRS.// theta) :-> markDP r'| (r',theta) <- observeAll (narrow1 (rules trs) (unmarkDP r))]

-- I should teach myself about comonads
-- http://sigfpe.blogspot.com/2008/03/comonadic-arrays.html
maps f xx = concat $ elems $ array (Pointer 1 (listArray (1, length xx) xx) =>> appF) where
    appF  = \(Pointer i a) ->  map elems [a // [(i, x)] | x <- f (a!i)]