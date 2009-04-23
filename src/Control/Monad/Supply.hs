{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Supply where

import Control.Applicative
import Control.Monad.List
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer

class Monad m => MonadSupply i m | m -> i where next :: m i; current :: m i

newtype Supply i a = Supply {runSupply_ :: State [i] a}
  deriving (Functor, Monad, MonadState [i], MonadSupply i)

instance MonadSupply e (State [e]) where
  current = head <$> get
  next    = get >>= \(_:x':xs) -> put (x':xs) >> return x'

instance (Monoid w, MonadSupply i m) => MonadSupply i (WriterT w m) where
  current = lift current
  next    = lift next

instance Monoid w => MonadSupply i (RWS r w [i]) where
  current = head <$> get
  next    = get >>= \(_:x':xs) -> put (x':xs) >> return x'

instance (MonadSupply i m) => MonadSupply i (ListT m) where
  current = lift current
  next    = lift next

runSupply :: (Num i, Bounded i, Enum i) => Supply i a -> a
runSupply m = evalState (runSupply_ m) [0..]

runSupply' m ids = evalState (runSupply_ m) ids