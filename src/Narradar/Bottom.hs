{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Narradar.Bottom where

import Control.Applicative
import Data.Foldable (Foldable(..))
import Data.HashTable (hashString)
import Data.Monoid
import Data.Traversable
import TRS
import Text.PrettyPrint (text)


data Bottom a = Bottom deriving (Show, Eq, Ord)
instance Functor Bottom  where fmap f Bottom = Bottom
instance Foldable Bottom where foldMap f Bottom = mempty
instance Traversable Bottom where traverse f Bottom = pure Bottom
instance Ppr Bottom      where pprF Bottom  = text "_|_"
instance Zip Bottom      where fzipWith f _ = fail "fzipWith: Bottoms don't zip"
instance HashTerm Bottom where hashF Bottom = hashString "Bottom"

bottom :: (Bottom :<: f) => Term f
bottom = inject Bottom