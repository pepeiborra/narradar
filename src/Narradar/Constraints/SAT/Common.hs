{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}

module Narradar.Constraints.SAT.Common
    ( module Narradar.Constraints.SAT.Common
    , module Satchmo.Binary
    , module Bool
    , module Satchmo.Code
    , module Satchmo.Data
    ) where

import Control.Applicative ((<$>))
import qualified Control.Exception as CE
import Control.Monad
import Data.Foldable (Foldable)
import Data.List (transpose,(\\))
import Data.Maybe (fromMaybe)

import Data.Term
import Satchmo.Binary hiding (constant)
import Satchmo.Boolean as Bool
import Satchmo.Code
import Satchmo.Data
import Narradar.Utils
import Narradar.Utils.Ppr
import Prelude hiding (and, not, or, lex, (>))


class SATOrd a where
    (>)  :: a -> a -> SAT Boolean
    (~~) :: a -> a -> SAT Boolean
    (>~) :: a -> a -> SAT Boolean
    a >~ b = orM [a > b, a ~~ b]

class Extend a where
    exgt :: (SATOrd a', Eq a') => a -> a -> [a'] -> [a'] -> SAT Boolean
    exeq :: (SATOrd a', Eq a') => a -> a -> [a'] -> [a'] -> SAT Boolean

-- -----
-- Utils
-- -----
assertOne = assert . (:[])
assertAll mm = mapM_ assertOne =<< sequence mm

oneM [] = constant False
oneM vv = do
  let n  = length vv
  fa    <- constant False
  tru   <- constant True
  ones  <- replicateM n boolean
  zeros <- replicateM n boolean
  andM (return(head ones) :
        [ andM [ return one_i  <<==>> ifte b_i zero_i1 one_i1
              , return zero_i <<==>> and[not b_i, zero_i1]]
         | (b_i, one_i, zero_i, one_i1, zero_i1) <-
             zip5 vv ones zeros (tail ones ++ [fa]) (tail zeros ++ [tru])])

zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee) = (a,b,c,d,e) : zip5 aa bb cc dd ee
zip5 _ _ _ _ _ = []

traceGt i1 i2 = pprTrace (ppr i1 <+> text ">" <+> ppr i2)

notM x  = not <$> x
orM  xx = or  =<< sequence xx
andM xx = and =<< sequence xx
allM f  = andM . map f
anyM f  = orM  . map f

ifte cond te el = andM [cond     ==> return te
                       ,not cond ==> return el]
ifM  cond te el = andM [    cond ==>> te
                       ,notM cond ==>> el]
ifM' cond te el = andM [return cond       ==>> te
                       ,return (not cond) ==>> el]

infix 0 ==>
infix 0 ==>>
a ==>> b = orM [notM a, b]
a ==>  b = orM [return (not a), b]

infix 0 <==>
a <==> b = -- andM [a ==> b, b ==> a]
          orM [and[a,b], and[not a, not b]]

infix 0 <<==>>
a <<==>> b = -- andM [a ==>> b, b ==>> a]
            orM [andM[a,b], andM[notM a, notM b]]

isSAT :: SAT a -> SAT a
isSAT = id

-- Testing
-- ---------
lexD lpo _      []     = True
lexD lpo []     _      = False
lexD lpo (f:ff) (g:gg) = lpo f g
                       || (f == g && lexD lpo ff gg)

mulD (>) m1 m2 = some  (m1\\m2) $ \x->
                 every (m2\\m1) $ \y->  x > y

some  = flip any
every = flip all