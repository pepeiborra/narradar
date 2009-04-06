{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.PrologIdentifiers where

import Control.Applicative
import Control.Parallel.Strategies
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable(..))
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable

import Narradar.DPIdentifiers
import TRS.Bottom
import TRS

type PS   = PIdentifier String
type PId  = Identifier PS

type BasicPS    = Var :+: T PS   :+: Hole
type BBasicPS   = Var :+: T PS   :+: Hole :+: Bottom
type BasicPId   = Var :+: T PId  :+: Hole
type BBasicPId  = Var :+: T PId  :+: Hole :+: Bottom
instance HashConsed BBasicPId
instance HashConsed BasicPId
instance HashConsed BBasicPS
instance HashConsed BasicPS

-- -------------------
-- Prolog Identifiers
-- -------------------
data PIdentifier a = InId a | OutId a | UId Int | FunctorId a deriving (Eq,Ord)

instance Show (PIdentifier String) where
  showsPrec p (InId a)      = (a ++) . ("_in" ++)
  showsPrec p (OutId a)     = (a ++) . ("_out" ++)
  showsPrec p (UId i)       = ("u_" ++) . showsPrec p i
  showsPrec p (FunctorId f) = (f ++)

instance Show a => Show (PIdentifier a) where
  showsPrec p (InId a)      = showsPrec p a . ("_in" ++)
  showsPrec p (OutId a)     = showsPrec p a .("_out" ++)
  showsPrec p (UId i)       = ("u_" ++) . showsPrec p i
  showsPrec p (FunctorId f) = showsPrec p f

instance NFData a => NFData (PIdentifier a) where
  rnf (InId a)  = rnf a
  rnf (OutId a) = rnf a
  rnf (UId   i) = rnf i
  rnf (FunctorId f) = rnf f

{-
instance DPSymbol PId where
  markDPSymbol (IdFunction f) = IdDP f
  markDPSymbol f = f
  unmarkDPSymbol (IdDP n) = IdFunction n
  unmarkDPSymbol n = n
  functionSymbol = IdFunction . FunctorId; dpSymbol = IdDP . FunctorId
  symbol (IdFunction (FunctorId f)) = f; symbol(IdDP (FunctorId f)) = f
  symbol _ = error "instance DPSymbol PId: trying to get the symbol of a prolog predicate"
-}


$(derive makeFunctor     ''PIdentifier)
$(derive makeFoldable    ''PIdentifier)
$(derive makeTraversable ''PIdentifier)
