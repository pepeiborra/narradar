{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Var where

import Data.Hashable
import Data.Term (Rename(..))
import Data.Term.Rules
import Data.Set as Set
import Narradar.Framework.Ppr

import qualified Data.Var.Family as Family

#ifdef HOOD
import Debug.Hood.Observe
#endif

data Var = Var (Maybe String) Int deriving Show
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
    pPrint (Var (Just l) _i) = text l -- <> char '_' <> int _i
    pPrint (Var _ i)        = char 'v' <> int i

instance Rename Var where
    rename (Var name i) (Var _ i') = Var ((++ show i') `fmap` name) i'

instance GetVars Var where getVars = Set.singleton

type instance Family.Var Var = Var

#ifdef HOOD
instance Observable Var where
  observer (Var ms i) = send "Var" (return Var << ms << i)
#endif
