{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances  #-}
{-# LANGUAGE ConstraintKinds #-}

module Narradar.Framework.Constraints
       ( module Narradar.Framework.Constraints
       , module Data.Constraint
       , module Control.Monad.ConstrainedNormal
       )where

import Control.Monad.ConstrainedNormal (NF(..), liftNF, lowerNF)
import Data.Constraint (Dict(..), (:-)(..))
import Data.Foldable(Foldable(..))
import Data.Term (GetVars)
import qualified Data.Term as Family

import Debug.Hoed.Observe

-- ------------------------
-- Constraint implication
-- ------------------------
class  c :=># a where ins :: c x :- a x
instance c :=># c where ins = Sub Dict

-- ---------------------
-- Framework constraints
-- ---------------------

class (GetVars a, Observable a, Observable(Family.Var a)) => GetVarsObservable a
instance (GetVars a, Observable a, Observable(Family.Var a)) => GetVarsObservable a

instance GetVarsObservable :=># GetVars where ins = Sub Dict

-- ------------------------
-- Flush a normal form
-- ------------------------

flushNF :: c a => (NF c f a -> f a) -> NF c f a -> NF c f a
flushNF lower = liftNF . lower

--instance Foldable (NF c f) where foldMap f (FMap g x) = foldMap f (g x)
