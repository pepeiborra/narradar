{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.Common
    ( module Narradar.Constraints.SAT.Common
    , module Satchmo.Binary
    , module Satchmo
    , module Satchmo.Code
    , module Satchmo.Data
    ) where

import Control.Applicative ((<$>), (<*), Applicative)
import qualified Control.Exception as CE
import Control.Monad.State
import Data.Foldable (Foldable, foldMap)
import Data.List (transpose,(\\))
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Term
import Satchmo.Binary hiding (constant)
import qualified Satchmo.Boolean as Satchmo
import Satchmo.Boolean hiding (SAT)
import Satchmo.Code
import Satchmo.Data
import Narradar.Utils
import Narradar.Framework.Ppr
import Prelude hiding (and, not, or, lex, (>))
import qualified Prelude as P

class SATOrd t a | a -> t where
    (>), (~~), (>~) :: a -> a -> SAT t Boolean
    a >~ b = orM [a > b, a ~~ b]

class Extend a where
    exgt, exeq :: (SATOrd t a', Eq a') => a -> a -> [a'] -> [a'] -> SAT t Boolean

data Status   = Mul | Lex (Maybe [Int]) deriving (Eq, Ord, Show)
mkStatus mul perm
 | mul       = Mul
 | otherwise = Lex (Just [head ([i | (i,True) <- zip [1..] perm_i] ++ [-1])
                             | perm_i <- perm])

-- ---------------------
-- Our custom SAT monad
-- ---------------------
data St t = St {termRPOcache :: Map (TermRPO t) Boolean, seenCache :: (Trues, Falses)}
type Falses = Set Boolean
type Trues  = Set Boolean

emptySt = St Map.empty mempty

instance Ord t => Monoid (St t) where
  mempty = St mempty mempty
  mappend st1 st2 = St{ termRPOcache = termRPOcache st1 `mappend` termRPOcache st2
                      , seenCache    = seenCache st1    `mappend` seenCache st2 }

newtype SAT t a = SAT {unSAT::StateT (St t) Satchmo.SAT a}
    deriving (Functor, Monad, MonadSAT, MonadState (St t), Applicative)

runSAT :: SAT t a -> Satchmo.SAT a
runSAT = (`evalStateT` emptySt) . unSAT

include, exclude :: [Boolean] -> SAT t ()
include bb = do
         st@St{seenCache=(ii,ee)} <- get
         put st{seenCache=(foldr Set.insert ii bb, ee)}

exclude bb = do
         st@St{seenCache=(ii,ee)} <- get
         put st{seenCache=(ii, foldr Set.insert ee bb)}

remove bb = do
  st@St{seenCache=(ii,ee)} <- get
  put st{seenCache=(foldr Set.delete ii bb, foldr Set.delete ee bb)}

withSeenCache m = do
  st <- get
  let (x,st') = runState m (seenCache st)
  put st{seenCache=st'}
  return x

isIncluded, isExcluded :: Boolean -> SAT t Bool
isIncluded b = withSeenCache $ do
  (ii,_) <- get
  return (b `Set.member` ii)

isExcluded b = withSeenCache $ do
  (_,ee) <- get
  return (b `Set.member` ee)

assertMemo b = do
  include [b]
  assert [b]

-- -------------------------
-- Reified RPO constraints
-- -------------------------
data TermRPO a = (:>)  a a
               | (:>~) a a
               | (:~~) a a
  deriving (Eq, Ord, Show)

memo key constraint = do
  st <- get
  case Map.lookup key (termRPOcache st) of
        Just b -> return b
        otherwise -> do
           b <- exists
           put st{termRPOcache = Map.insert key b (termRPOcache st)}
--           pprTrace (text "Map expanded with" <+> pPrint s <+> text ">" <+> pPrint t) (return ())
           assertAll [return b <<==>> constraint]
           return b

-- -----
-- Utils
-- -----

assertAll :: MonadSAT m => [m Boolean] -> m ()
assertAll mm = mapM_ (assert . (:[])) =<< sequence mm

oneM [] = constant False
oneM vv = do
  let n  = length vv
  fa    <- constant False
  tru   <- constant True
  ones  <- replicateM n boolean
  zeros <- replicateM n boolean
  andM (return(head ones) :
        [ andM [ return one_i  <<==>> ifM b_i (return zero_i1) (return one_i1)
              , return zero_i <<==>> andM[notM b_i, return zero_i1]]
         | (b_i, one_i, zero_i, one_i1, zero_i1) <-
             zip5 vv ones zeros (tail ones ++ [fa]) (tail zeros ++ [tru])])

zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee) = (a,b,c,d,e) : zip5 aa bb cc dd ee
zip5 _ _ _ _ _ = []

traceGt i1 i2 = pprTrace (pPrint i1 <+> text ">" <+> pPrint i2)

notM x  = not <$> x
orM  xx = or  =<< sequence xx
andM xx = and =<< sequence xx

allM f  = andM . map f
anyM f  = orM  . map f
everyM  = flip allM
someM   = flip someM

ifte cond te el = andM [cond     ==> return te
                       ,not cond ==> return el]
ifM  cond te el = andM [    cond ==>> te
                       ,notM cond ==>> el]
ifM' cond te el = andM [return cond       ==>> te
                       ,return (not cond) ==>> el]

ifMemo cond te el = andM [ [cond] *==> te
                         , [cond]  !==> el]

infix 1 ==>
infix 1 ==>>
a ==>> b = orM [notM a, b]
a ==>  b = orM [return(not a), b]

infix 1 *==>
infix 1 !==>
infix 1 *!==>

aa *==> b = (aa,[]) *!==> b
aa !==> b = ([],aa) *!==> b

infix 0 <==>
a <==> b = -- andM [a ==> b, b ==> a]
          orM [and[a,b], and[not a, not b]]

infix 0 <<==>>
a <<==>> b = -- andM [a ==>> b, b ==>> a]
            orM [andM[a,b], andM[notM a, notM b]]

andMemo bb m = do
  abort <- P.or <$> mapM isExcluded bb
  if abort
     then constant False
     else do include bb
             andM(m : map return bb)<* remove bb

andMemoNeg bb m = do
  abort <- P.or <$> mapM isIncluded bb
  if abort
     then constant False
     else do exclude bb
             andM(m : map (return.not) bb) <* remove bb

withFalse bb orelse m = do
  abort <- P.or <$> mapM isIncluded bb
  if abort
     then constant orelse
     else do
          exclude bb
          m <* remove bb

withTrue bb orelse m = do
  abort <- P.or <$> mapM isExcluded bb
  if abort
     then constant orelse
     else do include bb
             m <* remove bb

(yyaa,nnaa) *!==> b = do
  abort1 <- P.or <$> mapM isExcluded yyaa
  abort2 <- P.or <$> mapM isIncluded nnaa
  if abort1 || abort2
     then constant True
     else and (map not nnaa ++ yyaa) ==>> b'
 where
  b' = do
          exclude nnaa
          include yyaa
          b <* remove (nnaa ++ yyaa)

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