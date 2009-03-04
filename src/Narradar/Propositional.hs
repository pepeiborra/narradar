{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Narradar.Propositional where

import Control.Applicative
import Data.AlaCarte
import Text.PrettyPrint
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable
import Data.Traversable
import Prelude hiding (not, and, or, foldr)


data Prop v f = Var v | And f f | Or f f | Tru | Not f deriving (Show, Eq)
type Formula v = Expr (Prop v)

infixr 3 /\
infixr 2 \/

not  = In . Not
(/\) = (In.) . Or
(\/) = (In.) . And
true = In Tru
false= not true
var  = In . Var

and = foldr (/\) true
or  = foldr (\/) false

a --> b = not a \/ b

pprFormula :: Show v => Formula v -> Doc
pprFormula = foldExpr f where
  f (And a b) = a <+> char '^' <+> b
  f (Or a b)  = a <+> char 'v' <+> b
  f Tru       = text "True"
  f (Not x)   = text "!" <+> x
  f (Var v)   = text (show v)


$(derive makeFunctor     ''Prop)
$(derive makeFoldable    ''Prop)
$(derive makeTraversable ''Prop)

