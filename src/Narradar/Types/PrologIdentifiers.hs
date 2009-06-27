{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types.PrologIdentifiers where

import Control.Applicative
import Control.Parallel.Strategies
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable(..))
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Monoid
import Text.PrettyPrint

import Narradar.Types.DPIdentifiers
import Data.Term.Ppr

-- -------------------
-- Prolog Identifiers
-- -------------------
data PrologId a = InId a | OutId a | UId Int | FunctorId a deriving (Eq,Ord)

class IsPrologId id where
    isInId      :: id -> Bool
    isOutId     :: id -> Bool
    isUId       :: id -> Bool
    isFunctorId :: id -> Bool

instance IsPrologId (PrologId a) where
    isOutId OutId{} = True; isOutId _ = False
    isInId InId{}   = True; isInId _  = False
    isUId UId{}     = True; isUId _   = False
    isFunctorId FunctorId{} = True; isFunctorId _ = False

instance (Foldable l, IsPrologId a) => IsPrologId (l a) where
    isInId      = getAny . foldMap (Any . isInId)
    isOutId     = getAny . foldMap (Any . isOutId)
    isUId       = getAny . foldMap (Any . isUId)
    isFunctorId = getAny . foldMap (Any . isFunctorId)

instance Show (PrologId String) where
  showsPrec _ (InId a)      = (a ++) . ("_in" ++)
  showsPrec _ (OutId a)     = (a ++) . ("_out" ++)
  showsPrec p (UId i)       = ("u_" ++) . showsPrec p i
  showsPrec _ (FunctorId f) = (f ++)

instance Show a => Show (PrologId a) where
  showsPrec p (InId a)      = showsPrec p a . ("_in" ++)
  showsPrec p (OutId a)     = showsPrec p a .("_out" ++)
  showsPrec p (UId i)       = ("u_" ++) . showsPrec p i
  showsPrec p (FunctorId f) = showsPrec p f

instance Ppr a => Ppr (PrologId a) where
  ppr (InId a)  = ppr a <> text "_in"
  ppr (OutId a) = ppr a <> text "_out"
  ppr (UId i)   = text "u_" <> int i
  ppr (FunctorId f) = ppr f

instance NFData a => NFData (PrologId a) where
  rnf (InId a)  = rnf a
  rnf (OutId a) = rnf a
  rnf (UId   i) = rnf i
  rnf (FunctorId f) = rnf f

$(derive makeFunctor     ''PrologId)
$(derive makeFoldable    ''PrologId)
$(derive makeTraversable ''PrologId)
