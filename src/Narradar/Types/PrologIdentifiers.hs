{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types.PrologIdentifiers where

import Control.Applicative
import Control.Parallel.Strategies
import Data.AlaCarte (Expr)
import Data.Foldable(Foldable(..))
import Data.Traversable as T (Traversable(..), mapM)
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

class Ord (WithoutPrologId id) => RemovePrologId id where
  type WithoutPrologId id :: *
  removePrologId :: id -> Maybe (WithoutPrologId id)

instance Ord a => RemovePrologId (PrologId a) where
  type WithoutPrologId (PrologId a) = a
  removePrologId (InId x)      = Just x
  removePrologId (OutId x)     = Just x
  removePrologId (FunctorId x) = Just x
  removePrologId (UId _      ) = Nothing

instance (RemovePrologId a) => RemovePrologId (Identifier a) where
  type WithoutPrologId (Identifier a) = Identifier (WithoutPrologId a)
  removePrologId = T.mapM removePrologId

instance RemovePrologId String where
  type WithoutPrologId String = String
  removePrologId = Just

instance Ord (Expr p) => RemovePrologId (Expr p) where
  type WithoutPrologId (Expr p) = Expr p
  removePrologId = Just

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
