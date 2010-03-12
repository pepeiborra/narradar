{-# LANGUAGE MultiParamTypeClasses #-}

module Narradar.Types.Var where

import Data.Term (Rename(..))
import Data.Term.Rules
import Data.Set as Set
import Narradar.Framework.Ppr

data Var = Var (Maybe String) Int deriving Show
instance Eq  Var where Var _ i == Var _ j = i == j
instance Ord Var where compare (Var _ i) (Var _ j) = compare i j

instance Enum Var where
    fromEnum (Var _ i) = i
    toEnum = Var Nothing

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
    rename (Var name i) (Var _ i') = Var name i'

instance GetVars Var Var where getVars = Set.singleton