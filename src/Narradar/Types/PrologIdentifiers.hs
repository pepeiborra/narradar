{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Narradar.Types.PrologIdentifiers where

import           Control.Applicative
import           Control.Arrow                (first)
import           Control.DeepSeq
import           Data.AlaCarte                (Expr)
import           Data.Foldable(Foldable       (..), toList)
import           Data.Hashable
import           Data.Traversable             as T (Traversable(..), mapM)
import           Data.Maybe
import           Data.Monoid                  (Monoid(..), Any(..))
import           Data.Typeable

import           Narradar.Types.DPIdentifiers
import           Narradar.Framework.Ppr

import Debug.Hoed.Observe

-- -------------------
-- Prolog Identifiers
-- -------------------
data PrologId a = InId a | OutId a | UId Int | FunctorId a
                  deriving (Eq,Ord,Typeable, Functor, Foldable, Traversable)


instance Hashable a => Hashable (PrologId a) where
  hashWithSalt s (InId a)  = 1 `hashWithSalt` hashWithSalt s a
  hashWithSalt s (OutId a) = 2 `hashWithSalt` hashWithSalt s a
  hashWithSalt s (UId i)   = 3 `hashWithSalt` i
  hashWithSalt s (FunctorId a) = 4 `hashWithSalt` hashWithSalt s a

class Ord (WithoutPrologId id) => RemovePrologId id where
  type WithoutPrologId id :: *
  removePrologId :: id -> Maybe (WithoutPrologId id)

instance Ord a => RemovePrologId (PrologId a) where
  type WithoutPrologId (PrologId a) = a
  removePrologId (InId x)      = Just x
  removePrologId (OutId x)     = Just x
  removePrologId (FunctorId x) = Just x
  removePrologId (UId _      ) = Nothing

instance (RemovePrologId a) => RemovePrologId (DPIdentifier a) where
  type WithoutPrologId (DPIdentifier a) = DPIdentifier (WithoutPrologId a)
  removePrologId = T.mapM removePrologId

instance RemovePrologId StringId where
  type WithoutPrologId StringId = StringId
  removePrologId = Just

instance Ord (Expr p) => RemovePrologId (Expr p) where
  type WithoutPrologId (Expr p) = Expr p
  removePrologId = Just

class PrologSymbol id where
    isInId      :: id -> Bool
    isOutId     :: id -> Bool
    isFunctorId :: id -> Bool
    mapUId      :: (Int -> Int) -> id -> Maybe id
    getUId      :: id -> Maybe Int
    isUId       :: id -> Bool
    isUId       = isJust . getUId

setUId i = mapUId (const i)

instance PrologSymbol (PrologId a) where
    isOutId OutId{} = True; isOutId  _ = False
    isInId  InId{}  = True; isInId   _ = False
    getUId   (UId i) = Just i         ; getUId   _ = Nothing
    mapUId f (UId i) = Just(UId $ f i)
    isFunctorId FunctorId{} = True; isFunctorId _ = False

instance (Traversable l, PrologSymbol a) => PrologSymbol (l a) where
    isInId      = getAny . foldMap (Any . isInId)
    isOutId     = getAny . foldMap (Any . isOutId)
    getUId   x | [x'] <- toList x = getUId x'; getUId   _ = Nothing
    mapUId f x = mapUId f `T.mapM` x
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

instance Pretty (PrologId String) where
  pPrint (InId a)  = text a <> text "_in"
  pPrint (OutId a) = text a <> text "_out"
  pPrint (UId i)   = text "u_" <> int i
  pPrint (FunctorId f) = text f

instance Pretty a => Pretty (PrologId a) where
  pPrint (InId a)  = pPrint a <> text "_in"
  pPrint (OutId a) = pPrint a <> text "_out"
  pPrint (UId i)   = text "u_" <> int i
  pPrint (FunctorId f) = pPrint f

instance NFData a => NFData (PrologId a) where
  rnf (InId a)  = rnf a
  rnf (OutId a) = rnf a
  rnf (UId   i) = rnf i
  rnf (FunctorId f) = rnf f

-- Hood
instance Observable1 PrologId where
  observer1 (InId  a) = send "InId"  (return InId << a)
  observer1 (OutId a) = send "OutId" (return OutId << a)
  observer1 (UId   i) = send "UId"   (return UId << i)
  observer1 (FunctorId f) = send "FunctorId" (return FunctorId << f)
