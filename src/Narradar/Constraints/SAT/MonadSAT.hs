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
{-# LANGUAGE ConstraintKinds #-}

module Narradar.Constraints.SAT.MonadSAT
    ( module Narradar.Constraints.SAT.MonadSAT
    , Status(..), mkStatus
    , Circuit, ECircuit, NatCircuit, OneCircuit, RPOCircuit
    , RPOExtCircuit(..), ExistCircuit(..)
    , AssertCircuit(..) -- , assertCircuits
    , castCircuit, Clause
    , Tree, printTree, mapTreeTerms
    , Eval, evalB, evalN, BIEnv, EvalM
    , input, true, false, not, ite, eq, lt, gt, one
    , Shared, runShared, removeComplex
    , HasPrecedence(..), precedence
    , HasFiltering(..), listAF, inAF
    , HasStatus(..), useMul, lexPerm
    ) where

import           Control.Arrow                       (first,second)
import           Control.Monad.Reader                (MonadReader(..),liftM)
import           Data.Hashable
import           Data.List                           (foldl')
import           Data.Term                           (Term, HasId)
import qualified Data.Term                           as Family
import           Prelude                             hiding (and, not, or, any, all, lex, (>))

import           Narradar.Utils
import           Narradar.Framework.Ppr              as Ppr
import           Narradar.Constraints.RPO            (Status(..), mkStatus)

import           Funsat.ECircuit                     (BEnv, BIEnv, Eval, EvalF(..), runEval)
import           Funsat.Types                        (Clause,Solution(..))
import           Funsat.ECircuit                     (Co, Circuit(true,false,input,not,andL,orL), ECircuit(..), NatCircuit(..), ExistCircuit(..), castCircuit)
import qualified Funsat.ECircuit                     as Funsat
import           Funsat.RPOCircuit
import           Funsat.RPOCircuit.Internal
import           Funsat.RPOCircuit.Symbols           (Natural(..))
import qualified Funsat.ECircuit                     as ECircuit
import qualified Funsat.Types                        as Funsat
import qualified Funsat.RPOCircuit                   as Funsat

import qualified Prelude                             as P
import Data.Foldable (Foldable)

-- --------
-- MonadSAT
-- --------

class (Monad m, Functor m, ECircuit repr, OneCircuit repr, Hashable v, Ord v, Show v) =>
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
instance Hashable Var where hashWithSalt s (V i) = hashWithSalt s i

lit (V i) = Funsat.L i

instance Pretty Var where pPrint (V i) = text "v" <> i
type instance Family.Var Var = Var

type Weight = Int

-- ---------------------
-- Interpreting booleans
-- ---------------------
newtype Flip t a b = Flip {unFlip::t b a}

--type Precedence = [Integer]

class Decode a b where decode :: a -> EvalM (Family.Var a) b

instance Decode (Eval var) Bool where decode = evalB
instance Decode (Eval var) Int  where decode = evalN
--instance (Ord var, Show var, CastCircuit repr Eval) => Decode (repr var) Int var where decode = decode . (castCircuit :: repr var -> Eval var)
instance Decode a b => Decode [a] [b] where decode = mapM decode
--instance (Decode a a', Decode b b', Family.Var a ~ Family.Var b) => Decode (a, b) (a',b') where
--  decode (a, b) = do {va <- decode a; vb <- decode b; return (va,vb)}

--instance Decode var Bool var where decode = evalB . input
instance Decode Var Bool where decode = evalB . input
instance Decode Var Int  where decode = evalN . input
instance (Ord v, Show v) => Decode (Natural v) Int where decode = evalN . nat

evalDecode :: (Ord var, Hashable var, Show var, Decode (Eval var) b) => WrapEval (Term termF var) var -> EvalM var b
evalDecode = decode . unwrapEval

type instance Family.Var (Eval var) = var
type instance Family.Var (Natural v) = Natural v
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

(>), (>~), (~~) ::
        ( id    ~ Family.Id termF
        , v     ~ Family.Var id
        , termF ~ Family.TermF repr
        , CoRPO repr termF tv v, RPOCircuit repr
        , HasFiltering id, HasStatus id, HasPrecedence id
        , HasId termF, Foldable termF
        , Eq (Term termF tv)
        ) => Term termF tv -> Term termF tv -> repr v
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

