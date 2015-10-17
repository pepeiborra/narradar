{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
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
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.MonadSAT
    ( module Narradar.Constraints.SAT.MonadSAT
    , Status(..), mkStatus
    , Circuit, ECircuit, NatCircuit, OneCircuit, TermCircuit
    , ExistCircuit(..)
    , AssertCircuit(..) -- , assertCircuits
    , castCircuit, Clause
    , Tree, printTree, mapTreeTerms
    , Eval, evalB, evalN, BIEnv, EvalM
    , input, true, false, not, ite, eq, lt, gt, one
    , HasPrecedence(..), precedence
    , HasFiltering(..), listAF, inAF
    , HasStatus(..), useMul, lexPerm
    , IsSimple(..), HasLexMul(..)
    ) where

import           Control.DeepSeq
import           Data.Foldable                       (Foldable)
import           Data.Hashable
import           Data.HashMap                        (HashMap)
import           Data.Monoid                         (Monoid(..))
import           Data.Term                           (Term, HasId1)
import qualified Data.Term                           as Family
import           Data.Typeable
import           Prelude                             hiding (and, not, or, any, all, lex, (>))

import           Narradar.Framework.Ppr              as Ppr
import           Narradar.Types                      (TermN)

import           Funsat.ECircuit                     (BIEnv, Eval, )
import           Funsat.Types                        (Clause)
import           Funsat.ECircuit                     ( Circuit(true,false,input,not,andL,orL)
                                                     , ECircuit(..)
                                                     , NatCircuit(..), Natural(..)
                                                     , ExistCircuit(..)
                                                     , MaxCircuit(..)
                                                     , castCircuit)
import qualified Funsat.ECircuit                     as Funsat
import           Funsat.TermCircuit
import           Funsat.TermCircuit.Ext
import           Funsat.TermCircuit.RPO.Symbols      (Status(..), mkStatus)
import qualified Funsat.TermCircuit                  as Funsat

import           Debug.Hoed.Observe
import qualified Prelude                             as P

-- -----------
-- VarMaps
-- -----------
type k :->: v = HashMap k v

data VarMaps expr id var = VarMaps
    { termGtMap :: !((TermN id, TermN id) :->: expr)
    , termGeMap :: !((TermN id, TermN id) :->: expr)
    , termEqMap :: !((TermN id, TermN id) :->: expr)
    }
  deriving Show

instance Ord id => Monoid (VarMaps expr id var) where
 mempty = VarMaps mempty mempty mempty
 mappend (VarMaps gt1 ge1 eq1) (VarMaps gt2 ge2 eq2) =
   VarMaps (gt1 `mappend` gt2) (ge1 `mappend` ge2) (eq1 `mappend` eq2)

-- --------
-- MonadSAT
-- --------

class (Monad m, Functor m, ECircuit repr, OneCircuit repr, NatCircuit repr, MaxCircuit repr, Hashable v, Ord v, Show v) =>
 MonadSAT repr v m | m -> repr v where
  boolean_ :: String -> m v
  natural_ :: String -> m (Natural v)
  assert_  :: String -> [repr v] -> m ()
  assertW  :: Weight -> [repr v] -> m ()
  assertW _ = assert

boolean = boolean_ ""
natural = natural_ ""
assert = assert_ ""

-- ---------
-- Variables
-- ---------

class Taggable v where
  tagWith :: String -> v -> v

-- Ints with the following soft invariant: the first 1000 values are reserved
data Var = V (Maybe String) Int deriving (Typeable, Generic)

instance Taggable Var where
  tagWith tag (V _ i) = V (Just tag) i

instance Eq Var where
  V _ a == V _ b = a == b

instance Ord Var where
  compare (V _ a) (V _ b) = compare a b

instance Observable Var

instance Show Var where
  show (V Nothing  i) = "v" ++ show i
  show (V (Just s) i) = "v" ++ show i ++ escape s
   where escape = concatMap escapeChar
         escapeChar '#' = "hash"
         escapeChar c   = [c]

instance Read Var where
  readsPrec _p ('v':rest) =
    [(V Nothing  i, rest') | (i,rest') <- readsPrec 0 rest] ++
    [(V (Just more) i, []) | (i,more) <- readsPrec 0 rest, more /= "" ]
  readsPrec _ _ = []
  
instance Bounded Var where minBound = V Nothing 0; maxBound = V Nothing maxBound
instance Hashable Var where hashWithSalt s (V _ i) = hashWithSalt s i

instance Enum Var where
    fromEnum (V _ i) = i
    toEnum = V Nothing

--lit (V _ i) = Funsat.L i

instance Pretty Var where
  pPrint (V Nothing  i) = text "v" <> i
  pPrint (V (Just s) i) = text "v" <> i <> text s

instance NFData Var where rnf (V n i) = rnf n `seq` rnf i

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
type instance Family.Var (Natural v) = v
deriving instance Pretty v => Pretty (Natural v)
-- ------------
-- Combinators
-- ------------

assertAll :: (Observable (repr v)) => MonadSAT repr v m => [repr v] -> m ()
assertAll cc = mapM_ (assert . (:[])) cc

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
        , CoTerm repr termF tv v, TermCircuit repr
        , HasId1 termF, Foldable termF
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

