{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}

module Lattice where
import Control.Monad (liftM2)
import Data.Maybe
import Data.List

import Control.Exception (assert)

infixl 4 ===
infixr 5 \/
infixr 5 /\


class Eq a => Lattice a where
 bottom, top :: a
 meet,join   :: a -> a -> a
 lt          :: a -> a -> Maybe Bool
 x `lt` y    | m == x    = Just True
             | m == y    = Just False
             | otherwise = Nothing
  where m = meet x y


x `ltJoin` y | x == y    = True
             | otherwise = x `join` y == y

-- * These are approximate (incorrect) versions of meet/join
--    which only work with linear orderings
meetLinear a b | a `lt` b == Just True = a
               | otherwise= assert (a `lt` b == Just True) b

joinLinear a b | meet a b == a = b
               | otherwise     = a

{-
meet :: Lattice a => a -> a -> a
meet x y 
 | x == bottom = x
 | y == bottom = y
 | otherwise = case comp 
-}

instance (Bounded a, Ord a) => Lattice a where
  lt   = (Just.) . (<=)
  meet = min
  join = max
  bottom = minBound
  top    = maxBound

instance (Lattice a, Lattice b) => Lattice (a,b) where
  meet (a1,a2) (b1,b2) = (meet a1 b1, meet a2 b2)
  join (a1,a2) (b1,b2) = (join a1 b1, join a2 b2)
--  (a1,a2) `lt` (b1,b2) = (a1 `lt` b1) &.& (a2 `lt` b2) where (&.&)= liftM2 (&&)
  top    = (top, top)
  bottom = (bottom, bottom)

instance (Eq a, Bounded [a]) => Lattice [a] where
  meet = intersect
  join = union
--  x `lt` y = Just (all (`elem` y) x)
  bottom = minBound
  top    = maxBound
  
lub, glb :: Lattice a => [a] -> a
--lub [x] = x
lub = foldr join bottom 
--glb [x] = x
glb = foldr meet top 

insert :: Lattice a => a -> [a] -> [a]
insert x [] = [x]
insert x yy = let (sm, bg) = span (\y -> Just True == y `lt` x) yy
              in sm ++ x:bg
---------------------------
-- properties of Lattices
---------------------------

(\/),(/\) :: Lattice a => a -> a -> a
(\/) = join
(/\) = meet
x === y = fromMaybe False ((x `lt` y) &.& (y `lt` x)) where (&.&)= liftM2 (&&)

--prop_lattice_commutativity :: (Lattice a) => a -> a -> Bool
prop_lattice_commutativity a b = (a \/ b === b \/ a) && 
			 	 (a /\ b === b /\ a)

prop_lattice_associativity a b c = (a \/ (b \/ c) === (a \/ b) \/ c) &&
	 	 	    	   (a /\ (b /\ c) === (a /\ b) /\ c)

prop_lattice_absorption a b = (a \/ (a /\ b) === a) &&
		      	      (a /\ (a \/ b) === a)

prop_lattice_bounds a = (a \/ minBound === a) && 
			(a /\ minBound === minBound) &&
			(a \/ maxBound === maxBound) &&
			(a /\ maxBound === a)
