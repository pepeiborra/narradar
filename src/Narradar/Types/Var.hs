module Narradar.Types.Var where

import Data.Term.Ppr
import Text.PrettyPrint

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

instance Ppr Var where
    ppr (Var (Just l) _i) = text l -- <> char '_' <> int _i
    ppr (Var _ i)        = char 'v' <> int i
