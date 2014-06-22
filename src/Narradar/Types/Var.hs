{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Var where

import Data.Hashable
import Data.Term (Rename(..))
import Data.Term.Rules
import Data.Set as Set
import Data.Typeable (Typeable)
import Narradar.Framework.Ppr

import qualified Data.Var.Family as Family

import Debug.Hoed.Observe

data Var = Var (Maybe String) Int deriving (Show, Typeable)
instance Eq  Var where Var _ i == Var _ j = i == j
instance Ord Var where compare (Var _ i) (Var _ j) = compare i j

type instance Family.Var Var = Var

instance Enum Var where
    fromEnum (Var _ i) = i
    toEnum = Var Nothing

instance Hashable Var where hashWithSalt _ (Var _ i) = i

var :: Monad m => Int -> m Var
var  = return . Var Nothing
var' :: Monad m => Maybe String -> Int -> m Var
var' = (return.) . Var

varName :: Var -> Maybe String
varName (Var n _) = n

uniqueId (Var _ i) = i

instance Pretty Var where
    pPrint (Var (Just l) _i) = text l <> brackets(int _i)
    pPrint (Var _ i)        = char 'v' <> int i

instance PprTPDB Var where
    pprTPDB (Var (Just l) _i) = text l
    pprTPDB (Var _ i)        = char 'v' <> int i

instance Rename Var where
    rename (Var name i) (Var _ i') = Var name i'

instance GetVars Var where getVars = Set.singleton

type instance Family.Var Var = Var

instance Observable Var where
  observer (Var ms i) = send "Var" (return Var << ms << i)
