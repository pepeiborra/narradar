{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Supply where

import Control.Monad.State

class Monad m => MonadSupply i m | m -> i where next :: m i

newtype Supply i a = Supply {runSupply_ :: State [i] a}
  deriving (Functor, Monad, MonadState [i], MonadSupply i)

instance MonadSupply e (State [e]) where
  next = do
      elems <- get
      put (tail elems)
      return (head elems)

runSupply :: (Num i, Bounded i, Enum i) => Supply i a -> a
runSupply m = evalState (runSupply_ m) [0..]

runSupply' m ids = evalState (runSupply_ m) ids