{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}

module Narradar.Constraints.SAT.LPOAF where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Data.Foldable (Foldable, toList)
import Data.List (transpose, (\\))
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Narradar.Utils.Ppr

import Narradar.Constraints.SAT.Common
import Narradar.Constraints.SAT.Examples hiding (gt)
import Narradar.Types hiding (symbol, constant)
import Narradar.Utils
import qualified Narradar.Types.ArgumentFiltering as AF

import qualified Prelude
import Prelude hiding (lex, not, and, or, quot)


-- -------------------------------------------------
-- Encoding of MPO symbols
-- -------------------------------------------------

data Symbol a = Symbol { the_symbol   :: a
                       , encodePrec   :: Number
                       , decodeSymbol :: Decoder Integer}

instance Show a => Show (Symbol a) where
    show Symbol{the_symbol} = show the_symbol

instance Ppr a => Ppr (Symbol a) where
    ppr Symbol{the_symbol} = ppr the_symbol

instance Eq   a => Eq   (Symbol a) where
    a@Symbol{} == b@Symbol{} = the_symbol a == the_symbol b

instance Ord a => Ord (Symbol a) where
   compare a b = the_symbol a `compare` the_symbol b

instance Decode (Symbol a) Integer where decode = decodeSymbol

symbol sig x = do
  n_b <- number ( length
                $ takeWhile (>0)
                $ iterate (`Prelude.div` 2)
                $ Set.size (getDefinedSymbols sig))
  return $ Symbol
             { the_symbol   = x
             , encodePrec   = n_b
             , decodeSymbol = decode n_b }
