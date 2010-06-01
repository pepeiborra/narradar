{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.MonadSAT
    ( module Narradar.Constraints.SAT.MonadSAT
    , Status(..), mkStatus
    , Circuit, ECircuit, NatCircuit, OneCircuit, RPOCircuit
    , RPOExtCircuit(..), ExistCircuit(..)
    , AssertCircuit(..), assertCircuits
    , castCircuit, castRPOCircuit, Clause
    , Tree, printTree, mapTreeTerms
    , Eval, evalB, evalN, BIEnv, EvalM
    , input, true, false, not, ite, eq, lt, gt, one
    , Shared, runShared, removeComplex
    , HasPrecedence(..), precedence
    , HasFiltering(..), listAF, inAF
    , HasStatus(..), useMul, lexPerm
    ) where

import Control.Arrow (first,second)
import Data.NarradarTrie (HasTrie, (:->:))
import Data.List (foldl')
import Funsat.Circuit (BEnv)
import Funsat.Types (Clause,Solution(..))
import Prelude hiding (and, not, or, any, all, lex, (>))

--import Narradar.Types ((:->))
import Narradar.Utils
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..), mkStatus)
import Narradar.Constraints.SAT.RPOCircuit hiding (and,or, nat)

import qualified Funsat.ECircuit as ECircuit
import qualified Funsat.Types as Funsat
import qualified Data.NarradarTrie as Trie
import qualified Narradar.Constraints.SAT.RPOCircuit as Funsat
import qualified Prelude as P

-- --------
-- MonadSAT
-- --------

class (Monad m, Functor m, ECircuit repr, OneCircuit repr, HasTrie v, Ord v, Show v) =>
 MonadSAT repr v m | m -> repr v where
  boolean :: m v
  natural :: m (Natural v)
  assert  :: [repr v] -> m ()
  assertW :: Weight -> [repr v] -> m ()
  assertW _ = assert

-- Ints with the following soft invariant: the first 1000 values are reserved
newtype Var = V Int deriving (Eq, Ord, Num, Enum)

instance Show Var where show (V i) = "v" ++ show i
instance Read Var where
  readsPrec p ('v':rest) = [(V i, rest) | (i,rest) <- readsPrec 0 rest]
  readsPrec _ _ = []
instance Bounded Var where minBound = V 0; maxBound = V maxBound
instance HasTrie Var where
  newtype Var :->: x = VarTrie (Int :->: x)
  empty = VarTrie Trie.empty
  lookup (V i) (VarTrie t) = Trie.lookup i t
  insert (V i) v (VarTrie t) = VarTrie (Trie.insert i v t)
  toList (VarTrie t) = map (first V) (Trie.toList t)

newtype Natural v = Natural {encodeNatural::v} deriving (Eq,Ord,Show)

lit (V i) = Funsat.L i

instance Pretty Var where pPrint (V i) = text "v" <> i

nat :: (Ord v, HasTrie v, Show v) => NatCircuit repr => Natural v -> repr v
nat (Natural n) = ECircuit.nat n

type Weight = Int

-- ---------------------
-- Interpreting booleans
-- ---------------------
type Precedence = [Integer]

class Decode a b var | a b -> var where decode :: a -> EvalM var b

instance Decode (Eval var) Bool var where decode = evalB
instance Decode (Eval var) Int var  where decode = evalN
--instance (Ord var, Show var, CastCircuit repr Eval) => Decode (repr var) Int var where decode = decode . (castCircuit :: repr var -> Eval var)
instance Decode a b var => Decode [a] [b] var where decode = mapM decode
instance (Decode a a' var, Decode b b' var ) => Decode (a, b) (a',b') var where
  decode (a, b) = do {va <- decode a; vb <- decode b; return (va,vb)}

--instance Decode var Bool var where decode = evalB . input
instance Decode Var Bool Var where decode = evalB . input
instance Decode Var Int Var  where decode = evalN . input
instance (Ord v, HasTrie v, Show v) => Decode (Natural v) Int v where decode = evalN . nat

evalDecode :: (Ord var, HasTrie var, Show var, Decode (Eval var) b var) => Eval var -> EvalM var b
evalDecode x = decode x

-- ------------
-- Combinators
-- ------------

assertAll :: MonadSAT repr v m => [repr v] -> m ()
assertAll = mapM_ (assert . (:[]))

calcBitWidth = length . takeWhile (P.>0) . iterate (`div` 2) . pred

infix 9 >
infix 9 ~~
infixl 8 /\,\/
infixl 7 -->
infix 6 <-->

constant True  = true
constant False = false

(>)  = Funsat.termGt
(~~) = Funsat.termEq
(>~) = Funsat.termGe

and = andL
or  = orL
(/\) = Funsat.and
(\/) = Funsat.or

all  f = and . map f
any  f = or  . map f
some  = flip any
every = flip all

(-->) = onlyif
(<-->) = iff

none = andL . map not
-- ---------
-- Testing
-- ---------

data VerifyRPOAF a = VerifyRPOAF { thePairs, theFilteredPairs
                                 , falseDecreasingPairs
                                 , falseWeaklyDecreasingPairs
                                 , falseWeaklyDecreasingRules
                                 , missingUsableRules
                                 , excessUsableRules  :: [a]
                                 }
                   | FailedWithStatusMismatch String

mkVerifyRPOAF = VerifyRPOAF [] [] [] [] [] [] []

instance (Eq a, Pretty a) => Pretty (VerifyRPOAF a) where
  pPrint VerifyRPOAF{..}
    = vcat [ text "The pairs are: " $$ nest 2 (vcat thePairs)
           , if theFilteredPairs /= thePairs
              then text "We filter them and get: " $$
                   nest 2 (vcat theFilteredPairs)
              else Ppr.empty
           , if P.not (null falseDecreasingPairs)
              then text "These pairs are not decreasing:" $$
                   nest 2 (vcat falseDecreasingPairs)
              else Ppr.empty
           , if P.not (null falseWeaklyDecreasingPairs)
              then text "These pairs are not weakly decreasing:" $$
                   nest 2 (vcat falseWeaklyDecreasingPairs)
              else Ppr.empty
           , if P.not (null falseWeaklyDecreasingRules)
              then text "These rules are not weakly decreasing:" $$
                   nest 2 (vcat falseWeaklyDecreasingRules)
              else Ppr.empty
           , if P.not (null missingUsableRules)
              then text "These rules are actually usable:" $$
                   nest 2 (vcat missingUsableRules)
              else Ppr.empty
           , if P.not (null excessUsableRules)
              then text "These rules are not usable:" $$
                   nest 2 (vcat excessUsableRules)
              else Ppr.empty
           ]

  pPrint (FailedWithStatusMismatch msg) = text msg

isCorrect VerifyRPOAF{..} = null (falseDecreasingPairs ++ falseWeaklyDecreasingPairs ++ falseWeaklyDecreasingRules ++ excessUsableRules ++ missingUsableRules)
isCorrect FailedWithStatusMismatch{} = False

