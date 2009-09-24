{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances, FlexibleInstances #-}
module Narradar.Framework (
        module Narradar.Framework,
        module MuTerm.Framework.Problem,
        module MuTerm.Framework.Processor,
        module MuTerm.Framework.Proof,
        module MuTerm.Framework.Strategy)
  where

import Control.Monad

import MuTerm.Framework.Problem
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy

import Narradar.Framework.Ppr


class Dispatch thing where
    dispatch :: MonadPlus m => thing -> Proof m ()


mkDispatcher :: Monad m => (a -> Proof m b) ->  a -> Proof m ()
mkDispatcher f = fmap (const ()) . f
