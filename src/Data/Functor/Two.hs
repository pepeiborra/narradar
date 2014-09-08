{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}
module Data.Functor.Two where

import Control.DeepSeq
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Debug.Hoed.Observe
import Narradar.Framework.Ppr

data Two a = Two { item1, item2 :: a}
           deriving (Eq,Show,Ord,Functor,Foldable,Traversable,Generic,Generic1,Typeable)

instance NFData a => NFData (Two a) where rnf (Two a b) = rnf a `seq` rnf b `seq` ()
instance Pretty a => Pretty(Two a)  where pPrint (Two a b) = parens(a <> comma <+> b)

instance Observable1 Two
instance Observable a => Observable (Two a) where
  observer = observer1
  observers = observers1
