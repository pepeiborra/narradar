{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.Common
    ( module Narradar.Constraints.SAT.Common
    , module Narradar.Constraints.RPO
    , Boolean, boolean, and, or, not, constant, assert
    , Number, number, eq, gt
    , Decoder, Decode, Satchmo.Code.decode
    ) where

import Control.Applicative ((<$>), (<*), Applicative)
import qualified Control.Exception as CE
import Control.Monad.State.Strict
import Data.Foldable (Foldable, foldMap)
import Data.List (intersect, transpose,(\\))
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Strict (Pair(..), (:!:))

import Data.Term
import qualified Satchmo.Boolean as Satchmo
import Satchmo.Boolean(MonadSAT, Boolean(..), boolean, and, or, not, xor, constant, assert)
import Satchmo.Binary(Number(..), number, eq, gt)
import Satchmo.Code
import Satchmo.Data
import Narradar.Utils
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..), mkStatus, HasPrecedence(..), HasStatus(..))

import Prelude hiding (and, not, or, lex, (>))
import qualified Prelude as P

class MonadSAT m => SATOrd m a | a -> m where
    (>), (~~), (>~) :: a -> a -> m Boolean
    a >~ b = orM [a > b, a ~~ b]

class Extend a where
    exgt, exeq :: (SATOrd (SAT id t) a', Eq a') => a -> a -> [a'] -> [a'] -> SAT id t Boolean

-- ---------------------
-- Our custom SAT monad
-- ---------------------
data St  id t = St { symPrecCache :: Map (OrderConstraint id) Boolean
                   , termRPOcache :: Map (OrderConstraint t)  Boolean
                   , seenCache    :: Trues :!: Falses}

type Falses = Set Boolean
type Trues  = Set Boolean

emptySt = St Map.empty Map.empty mempty

instance (Ord id, Ord t) => Monoid (St id t) where
  mempty = St mempty mempty mempty
  mappend st1 st2 = St{ symPrecCache = symPrecCache st1 `mappend` symPrecCache st2
                      , termRPOcache = termRPOcache st1 `mappend` termRPOcache st2
                      , seenCache    = seenCache st1    `mappend` seenCache st2 }

newtype SAT id t a = SAT {unSAT::StateT (St id t) Satchmo.SAT a}
    deriving (Functor, Monad, MonadSAT, MonadState (St id t), Applicative)

runSAT :: Pretty t => SAT id t a -> Satchmo.SAT a
runSAT = (`evalStateT` emptySt) . unSAT


runSAT' (SAT m) = do
  (v, st) <- runStateT m emptySt
  return $ do
    let (kk,vv) = unzip $ Map.toList (termRPOcache st)
    vv' <- mapM decode vv
    pprTrace (Map.fromList $ zip kk vv') v

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

assertMemo b = do
  include [b]
  assert [b]

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

oneM = one >=> and

one [] = constant False >>= \c -> return [c]
one vv = do
  let n  = length vv
  fa    <- constant False
  tru   <- constant True
  ones  <- replicateM n boolean
  zeros <- replicateM n boolean

  clauses <- sequence $ concat
            [ [return one_i  <<==>> ifte b_i zero_i1 one_i1
              ,return zero_i <<==>> and [not b_i, zero_i1]]
             | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                 zip5 vv ones zeros (tail ones ++ [fa]) (tail zeros ++ [tru])]

  return (head ones : clauses)


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

ifte cond te el = andM [     cond ==> return te
                       , not cond ==> return el]

ifM = ((join.).) . liftM3 ifte

ifM' cond = (join.) . liftM2 (ifte cond)

ifMemo cond te el = andM [ [cond] *==> te
                         , [cond] !==> el]

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
a <==> b = not <$> xor [a, b]

infix 0 <<==>>
(<<==>>) = (join.) . liftM2 (<==>)


andMemo bb m = do
  abort <- P.or <$> mapM isExcluded bb
  if abort
     then constant False
     else do include bb
             andM(m : map return bb) <* remove bb

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



-- ---------
-- Testing
-- ---------

data VerifyRPOAF a = VerifyRPOAF { falseDecreasingPairs :: [a]
                                 , falseWeaklyDecreasingRules :: [a]
                                 , missingUsableRules :: [a]
                                 , excessUsableRules  :: [a]
                                 }
                   | FailedWithStatusMismatch String

instance Pretty a => Pretty (VerifyRPOAF a) where
  pPrint VerifyRPOAF{..} = vcat [ if P.not (null falseDecreasingPairs)
                                    then text "These pairs are not decreasing:" $$ nest 2 (vcat falseDecreasingPairs)
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

isCorrect VerifyRPOAF{..} = null (falseDecreasingPairs ++ falseWeaklyDecreasingRules ++ excessUsableRules ++ missingUsableRules)
isCorrect FailedWithStatusMismatch{} = False


