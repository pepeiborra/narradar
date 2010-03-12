{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narradar.Constraints.SAT.Combinators
    ( module Narradar.Constraints.SAT.Combinators
    , module Narradar.Constraints.SAT.Solve
    , Status(..), mkStatus
    , Circuit, ECircuit, NatCircuit, OneCircuit, RPOCircuit
    , RPOExtCircuit(..), ExistCircuit(..)
    , castCircuit, Clause
    , Eval, evalB, evalN, BIEnv
    , input, true, false, not, ite, eq, lt, gt, lit, one
    , Shared, runShared, removeComplex
    , HasPrecedence(..), precedence
    , HasFiltering(..), listAF, inAF
    , HasStatus(..), useMul, lexPerm
    ) where

import Data.List (foldl')
import qualified Funsat.Types as Funsat
import Funsat.Types (Clause)

import Data.Term
import Narradar.Utils
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..), mkStatus)
import Narradar.Constraints.SAT.Solve
import Narradar.Constraints.SAT.RPOCircuit hiding (and,or, nat)
import qualified Narradar.Constraints.SAT.RPOCircuit as Funsat

import Prelude hiding (and, not, or, any, all, lex, (>))
import qualified Prelude as P

-- ------------
-- Combinators
-- ------------

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

