{-# LANGUAGE UndecidableInstances #-}

module Data.UniqueList where

import Data.Foldable (Foldable)
import qualified Data.List as List
import Data.Monoid
import Data.Set as Set (Set, fromList)
import Data.Traversable
import Narradar.Framework.Ppr
import Prelude

instance Ppr [a] => Ppr (UniqueList a) where ppr = ppr . toList

newtype UniqueList a = UniqueList {toList :: [a]}
  deriving (Eq, Ord, Read, Show)

instance Eq a => Monoid (UniqueList a) where
  mempty = UniqueList mempty
  mappend (UniqueList l1) (UniqueList l2) = UniqueList $ List.nub (l1++l2)

fromList, fromUniqueList :: Eq a => [a] -> UniqueList a
toSet :: Ord a => UniqueList a -> Set a

fromUniqueList = UniqueList
fromList       = UniqueList . List.nub
toSet          = Set.fromList . Data.UniqueList.toList

head = liftList Prelude.head
tail = liftList Prelude.tail
length = Prelude.length . toList
null = Prelude.null . toList
find f (UniqueList x) = List.find f x
cons x ul@(UniqueList xx)
    | x `Prelude.elem` xx = ul
    | otherwise   = UniqueList (x:xx)

UniqueList l1 \\ UniqueList l2 = UniqueList (l1 List.\\ l2)

elem x (UniqueList l) = Prelude.elem x l
notElem x l = not(Data.UniqueList.elem x l)

liftList f (UniqueList l) = UniqueList (f l)

