{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Data.Functor1 where

import Data.Typeable
import GHC.Exts (Constraint)

class Functor1 r where fmap1 :: (forall a . f a -> g a) -> r f -> r g

data NF1 :: ((* -> *) -> Constraint) -> ((* -> *) -> *) -> (* -> *) -> * where
  FMap1 :: constraint g => (forall a. g a -> f a) -> t g -> NF1 constraint t f

  deriving Typeable

liftNF1 :: c f => t f -> NF1 c t f
liftNF1 tf = FMap1 id tf

lowerNF1 :: (forall f. c f => (forall a. f a -> g a) -> t f -> t g) -> NF1 c t g -> t g
lowerNF1 fmp1 (FMap1 g tf) = fmp1 g tf

instance Functor1 (NF1 c t) where fmap1 f (FMap1 g t) = FMap1 (f.g) t
