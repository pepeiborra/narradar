module Narradar.Var where

import Data.Term.Ppr
import Text.PrettyPrint

data Var = Var (Maybe String) Int deriving (Eq,Show)
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

instance Ppr Var where
    ppr (Var (Just l) i) = text l -- <> char '_' <> int i
    ppr (Var _ i)        = char 'v' <> int i
