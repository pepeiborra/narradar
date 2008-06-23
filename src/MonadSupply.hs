{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module MonadSupply where

import Control.Monad.State

class MonadSupply i m | m -> i where next :: m i

newtype Supply i a = Supply {runSupply_ :: State [i] a}
  deriving (Functor, Monad, MonadSupply i)

instance MonadSupply e (State [e]) where
  next = do
      elems <- get
      put (tail elems)
      return (head elems)

runSupply :: (Num i, Bounded i, Enum i) => Supply i a -> a
runSupply m = evalState (runSupply_ m) [0..]