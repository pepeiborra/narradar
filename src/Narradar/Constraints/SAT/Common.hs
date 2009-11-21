{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.Common
    ( module Narradar.Constraints.SAT.Common
    , module Narradar.Constraints.RPO
    , module Satchmo.Boolean
    , MonadSAT(..)
    , Number, number, eq, gt
    , Decoder, Decode, Satchmo.Code.decode
    ) where

import Control.Applicative ((<$>), (<*), Applicative)
import qualified Control.Exception as CE
import Control.Monad.State.Strict
import Data.Foldable (Foldable, foldMap)
import qualified Data.Foldable as F
import Data.List (intersect, sort, transpose,(\\))
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Strict (Pair(..), (:!:))

import Data.Term
import qualified Satchmo.Boolean as Satchmo
import Satchmo.Boolean(MonadSAT, Boolean(..), boolean, not, constant, assert, assertW)
import Satchmo.Binary(Number(..), number, eq, gt)
import Satchmo.Code
import Satchmo.Data
import qualified Satchmo.SAT.Weighted as Satchmo
import Narradar.Utils
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..), mkStatus, HasPrecedence(..), HasStatus(..), HasFiltering(..))

import Prelude hiding (and, not, or, lex, (>))
import qualified Prelude as P

class MonadSAT m => SATOrd m a | a -> m where
    (>), (~~), (>~) :: a -> a -> m Boolean
    a >~ b = Satchmo.or =<< sequence [a > b, a ~~ b]

class Extend a where
    exgt, exeq :: (SATOrd (SAT id t) a', Eq a') => a -> a -> [a'] -> [a'] -> SAT id t Boolean

-- ---------------------
-- Our custom SAT monad
-- ---------------------
data St  id t = St { symPrecCache :: Map (OrderConstraint id) Boolean
                   , termRPOcache :: Map (OrderConstraint t)  Boolean
                   , seenCache    :: Trues :!: Falses
                   , andCache     :: EnumMap Boolean (EnumMap Boolean Boolean)
                   , eqCache      :: Map (Boolean, Boolean) Boolean }

type Falses = Set Boolean
type Trues  = Set Boolean

emptySt = St mempty mempty mempty mempty mempty

instance (Ord id, Ord t) => Monoid (St id t) where
  mempty = emptySt
  mappend st1 st2 = St{ symPrecCache = symPrecCache st1 `mappend` symPrecCache st2
                      , termRPOcache = termRPOcache st1 `mappend` termRPOcache st2
                      , seenCache    = seenCache    st1 `mappend` seenCache st2
                      , andCache     = andCache     st1 `mappend` andCache st2
                      , eqCache      = eqCache      st1 `mappend` eqCache st2}

newtype SAT id t a = SAT {unSAT::StateT (St id t) SatchmoSAT a}
    deriving (Functor, Monad, MonadSAT, MonadState (St id t), Applicative)

type SatchmoSAT = Satchmo.SAT

#ifdef DEBUG
runSAT (SAT m) = do
  (v, st) <- runStateT m emptySt
  let msg = vcat [text "Stats of the SAT cache:"
                 ,text "RPO constraints cached:" <+> Map.size (termRPOcache st)
                 ,text "Order constraints cached:" <+> Map.size (symPrecCache st)
                 ,text "Propositional formulas cached:" <+> F.sum (fmap EnumMap.size (andCache st))
                 ]
  pprTrace msg $ return v

runSAT' (SAT m) = do
  (v, st) <- runStateT m emptySt
  return $ do
    let (kk,vv) = unzip $ Map.toList (termRPOcache st)
    vv' <- mapM decode vv
    pprTrace (Map.fromList $ zip kk vv') v

#else
runSAT :: (Ord id, Ord t, Pretty t) => SAT id t a -> Satchmo.SAT a
runSAT = (`evalStateT` emptySt) . unSAT
#endif

include, exclude :: [Boolean] -> SAT id t ()
include bb = do
         st@St{seenCache=(ii :!: ee)} <- get
         CE.assert (Prelude.all (`Set.notMember` ee) bb) $
          put st{seenCache=(foldr Set.insert ii bb :!: ee)}

exclude bb = do
         st@St{seenCache=(ii :!: ee)} <- get
         CE.assert (Prelude.all (`Set.notMember` ii) bb) $
          put st{seenCache=(ii :!: foldr Set.insert ee bb)}

remove bb = do
  st@St{seenCache=(ii :!: ee)} <- get
  let bb_set = Set.fromList bb
  put st{seenCache=(Set.difference ii bb_set :!: Set.difference ee bb_set)}

withSeenCache m = do
  st <- get
  let (x,st') = runState m (seenCache st)
  put st{seenCache=st'}
  return x

isIncluded, isExcluded :: Boolean -> SAT id t Bool
isIncluded b = withSeenCache $ do
  (ii :!: _) <- get
  return (b `Set.member` ii)

isExcluded b = withSeenCache $ do
  (_ :!: ee) <- get
  return (b `Set.member` ee)

assertMemo b = assert [b]
{-
assertMemo b = do
  include [b]
  assert [b]
-}
-- -------------------------
-- Reified RPO constraints
-- -------------------------
data OrderConstraint a = (:>)  a a
                       | (:>~) a a
                       | (:~~) a a
  deriving (Eq, Ord, Show)

instance Pretty a => Pretty (OrderConstraint a) where
  pPrint (a :> b) = a <+> text ">" <+> b
  pPrint (a :>~ b) = a <+> text ">=" <+> b
  pPrint (a :~~ b) = a <+> text "==" <+> b

memoSym key constraint = do
  st <- get
  case Map.lookup key (symPrecCache st) of
        Just b -> return b
        otherwise -> do
           b <- boolean
           put st{symPrecCache = Map.insert key b (symPrecCache st)}
           c <- constraint
           assert [not c, b]
           assert [not b, c]
           return b

memoTerm key constraint = do
  st <- get
  case Map.lookup key (termRPOcache st) of
        Just b -> return b
        otherwise -> do
           b <- boolean
           put st{termRPOcache = Map.insert key b (termRPOcache st)}
           c <- constraint
           assert [not c, b]
           assert [not b, c]
           return b

-- -----
-- Utils
-- -----
calcBitWidth = length . takeWhile (P.>0) . iterate (`div` 2) . pred

assertAll :: MonadSAT m => [m Boolean] -> m ()
assertAll mm = mapM_ (assert . (:[])) =<< sequence mm

some  = flip any
every = flip all

oneM = one >=> and_

one [] = constant False >>= \c -> return [c]
one vv = do
  let n  = length vv
  fa    <- constant False
  tru   <- constant True
  ones  <- replicateM n boolean
  zeros <- replicateM n boolean


  clauses <- sequence $ concat
            [ [return one_i  <=^=> ifte_ b_i zero_i1 one_i1
              ,return zero_i <=^=> and_ [not b_i, zero_i1]]
             | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                 zip5 vv ones zeros (tail ones ++ [fa]) (tail zeros ++ [tru])]

  return (head ones : clauses)


zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee) = (a,b,c,d,e) : zip5 aa bb cc dd ee
zip5 _ _ _ _ _ = []

traceGt i1 i2 = pprTrace (pPrint i1 <+> text ">" <+> pPrint i2)

notM x  = not <$> x

or_ []  = constant False
or_ [x] = return x
or_  x  = Satchmo.or x
orM_ xx = or_ =<< sequence xx

or []  = constant False
or [x] = return x
or x   = (notM . and . map not) x
orM xx = or =<< sequence xx

and_ [] = constant True
and_ [x]= return x
and_  x = Satchmo.and x
andM_ xx = and_ =<< sequence xx


and []  = constant True
and [x] = return x
and (sort -> (x:xx)) = foldM and2 x xx
--and x = and_ x
andM xx = and =<< sequence xx

and2 (Constant True) b    = return b
and2 a@(Constant False) b = return a
and2 a (Constant True)    = return a
and2 a b@(Constant False) = return b
and2 a b = do
  st <- get
  case EnumMap.lookup a (andCache st) of
    Just a_cache  -> case EnumMap.lookup b a_cache of
         Just v -> return v
         _      -> do
             ab <- Satchmo.and [a,b]
             let a_cache' = EnumMap.insert b ab a_cache
             modify (\st -> st{andCache = EnumMap.insert a a_cache' (andCache st)})
             return ab
    _ -> do
      ab <- Satchmo.and [a,b]
      modify (\st -> st{andCache = EnumMap.insert a (EnumMap.singleton b ab) (andCache st)})
      return ab

xor  = Satchmo.xor
xor_ = Satchmo.xor

allM f  = andM . map f
anyM f  = orM  . map f
everyM  = flip allM
someM   = flip someM

allM_ f  = andM_ . map f
anyM_ f  = orM_  . map f
everyM_  = flip allM_
someM_   = flip someM_

ifte cond te el = andM [     cond ==> return te
                       , not cond ==> return el]

ifte_ cond te el = andM_ [     cond ^==> return te
                         , not cond ^==> return el]

ifM  = ((join.).) . liftM3 ifte
ifM_ = ((join.).) . liftM3 ifte_

ifM'  cond = ifM  (return cond)
ifM_' cond = ifM_ (return cond)

ifMemo = ifM'
{-
ifMemo cond te el = andM [ [cond] *==> te
                         , [cond] !==> el]
-}

infix 7 ==>
infix 7 ==>>
a ==>> b = do {va <- a; vb <- b; va --> vb}
a ==> b  = do {vb <- b; a --> vb}
Constant True  --> b = return b
Constant False --> b = constant True
a --> b = notM $ and [a, not b]

infix 7 ^==>
infix 7 ^==>>
a ^==>> b = do {va <- a; vb <- b; va ^--> vb}
a ^==> b  = do {vb <- b; a ^--> vb}
Constant True  ^--> b = return b
Constant False ^--> b = constant True
a ^-->  b = or_ [not a, b]


infix 7 *==>
infix 7 !==>
infix 7 *!==>

aa *==> b = (aa,[]) *!==> b
aa !==> b = ([],aa) *!==> b

infix 7 ^*==>
infix 7 ^!==>
infix 7 ^*!==>

aa ^*==> b = (aa,[]) ^*!==> b
aa ^!==> b = ([],aa) ^*!==> b

infix 6 <-->
infix 6 <-^->
Constant False <-^-> b = return (not b)
Constant True  <-^-> b = return b
b <-^-> Constant False = return (not b)
b <-^-> Constant True  = return b
a <-^-> b = not <$> xor_ [a, b]

Constant False <--> b = return (not b)
Constant True  <--> b = return b
b <--> Constant False = return (not b)
b <--> Constant True  = return b
--a <--> b = a <-^-> b
a <--> b = do
  let it = if a < b then (a,b) else (b,a)
  st <- get
  case Map.lookup it (eqCache st) of
    Just v -> return v
    Nothing -> do
       v <- not <$> Satchmo.xor [a, b]
       put st{eqCache = Map.insert it v (eqCache st)}
       return v


infix 6 <==>
infix 6 <=^=>
(<==>) = (join.) . liftM2 (<-->)
(<=^=>) = (join.) . liftM2 (<-^->)

{-# INLINE andMemo #-}
andMemo bb m = andM (m : map return bb)
{-
andMemo bb m = do
  abort <- P.or <$> mapM isExcluded bb
  if abort
     then constant False
     else do include bb
             andM(m : map return bb) <* remove bb
-}

{-# INLINE andMemoNeg #-}
andMemoNeg bb m = andM (m : map (return.not) bb)
{-
andMemoNeg bb m = do
  abort <- P.or <$> mapM isIncluded bb
  if abort
     then constant False
     else do exclude bb
             andM(m : map (return.not) bb) <* remove bb
-}
withFalse _ _ m = m
{-
withFalse bb orelse m = do
  abort <- P.or <$> mapM isIncluded bb
  if abort
     then constant orelse
     else do
          exclude bb
          m <* remove bb
-}
withTrue _ _ m = m
{-
withTrue bb orelse m = do
  abort <- P.or <$> mapM isExcluded bb
  if abort
     then constant orelse
     else do include bb
             m <* remove bb
-}

{-# INLINE (*!==>) #-}

(yyaa,nnaa) *!==> b = and (map not nnaa ++ yyaa) ==>> b
(yyaa,nnaa) ^*!==> b = and_ (map not nnaa ++ yyaa) ^==>> b

{-
(yyaa,nnaa) *!==> b
  | P.not (null(yyaa `intersect` nnaa)) = constant True
  | otherwise = do
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
-}


-- ---------
-- Testing
-- ---------

data VerifyRPOAF a = VerifyRPOAF { the_pairs, the_filtered_pairs
                                 , falseDecreasingPairs
                                 , falseWeaklyDecreasingPairs
                                 , falseWeaklyDecreasingRules
                                 , missingUsableRules
                                 , excessUsableRules  :: [a]
                                 }
                   | FailedWithStatusMismatch String

mkVerifyRPOAF = VerifyRPOAF [] [] [] [] [] [] []

instance (Eq a, Pretty a) => Pretty (VerifyRPOAF a) where
  pPrint VerifyRPOAF{..} = vcat [ text "The pairs are: " $$ nest 2 (vcat the_pairs)
                                , if the_filtered_pairs /= the_pairs
                                    then text "We filter them and get: " $$ nest 2 (vcat the_filtered_pairs)
                                    else Ppr.empty
                                , if P.not (null falseDecreasingPairs)
                                    then text "These pairs are not decreasing:" $$ nest 2 (vcat falseDecreasingPairs)
                                    else Ppr.empty
                                , if P.not (null falseWeaklyDecreasingPairs)
                                    then text "These pairs are not weakly decreasing:" $$ nest 2 (vcat falseWeaklyDecreasingPairs)
                                    else Ppr.empty
                                , if P.not (null falseWeaklyDecreasingRules)
                                    then text "These rules are not weakly decreasing:" $$ nest 2 (vcat falseWeaklyDecreasingRules)
                                    else Ppr.empty
                                , if P.not (null missingUsableRules)
                                    then text "These rules are actually usable:" $$ nest 2 (vcat missingUsableRules)
                                    else Ppr.empty
                                , if P.not (null excessUsableRules)
                                    then text "These rules are not usable:" $$ nest 2 (vcat excessUsableRules)
                                    else Ppr.empty
                                ]
  pPrint (FailedWithStatusMismatch msg) = text msg

isCorrect VerifyRPOAF{..} = null (falseDecreasingPairs ++ falseWeaklyDecreasingPairs ++ falseWeaklyDecreasingRules ++ excessUsableRules ++ missingUsableRules)
isCorrect FailedWithStatusMismatch{} = False


