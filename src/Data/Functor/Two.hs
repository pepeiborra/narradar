{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Functor.Two where

import Control.Applicative
import Control.DeepSeq
import Data.Foldable
import Data.Term.Family
import Data.Traversable
import Data.Typeable
import Debug.Hoed.Observe
import Narradar.Framework.Ppr

data Two a = Two { item1, item2 :: a}
           deriving (Eq,Show,Ord,Functor,Foldable,Traversable,Generic,Generic1,Typeable)

type instance Var (Two a) = Var a
type instance TermF (Two a) = TermF a


instance Applicative Two where
  pure x = Two x x
  Two f g <*> Two a b = Two (f a) (g b)

instance NFData a => NFData (Two a) where rnf (Two a b) = rnf a `seq` rnf b `seq` ()
instance Pretty a => Pretty(Two a)  where pPrint (Two a b) = parens(a <> comma <+> b)

instance Observable1 Two
instance Observable a => Observable (Two a) where
  observer = observer1
  observers = observers1
