{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE PatternGuards  #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}


module Narradar.Types.PrologIdentifiers where

import Control.Applicative
import Control.Arrow (first)
import Control.Parallel.Strategies
import Data.AlaCarte (Expr)
import Data.Foldable(Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Maybe
import Data.NarradarTrie (HasTrie, (:->:) )
import qualified Data.NarradarTrie as Trie
import Data.Monoid
import Data.Typeable

import Narradar.Types.DPIdentifiers
import Narradar.Framework.Ppr

-- -------------------
-- Prolog Identifiers
-- -------------------
data PrologId a = InId a | OutId a | UId Int | FunctorId a deriving (Eq,Ord,Typeable)

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

instance DPSymbol a => DPSymbol (PrologId a) where
  markDPSymbol = fmap markDPSymbol
  unmarkDPSymbol = fmap unmarkDPSymbol

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
    isInId InId{}   = True; isInId   _ = False
    getUId   (UId i) = Just i         ; getUId   _ = Nothing
    mapUId f (UId i) = Just(UId $ f i); mapUId _ _ = Nothing
    isFunctorId FunctorId{} = True; isFunctorId _ = False

instance (Traversable l, PrologSymbol a) => PrologSymbol (l a) where
    isInId      = getAny . foldMap (Any . isInId)
    isOutId     = getAny . foldMap (Any . isOutId)
    getUId   x | [x'] <- toList x = getUId   x'; getUId   _ = Nothing
    mapUId f x = mapUId f `T.mapM` x; mapUId _ _ = Nothing
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

instance HasTrie a => HasTrie (PrologId a) where
  data PrologId a :->: x = PrologIdTrie (a :->: x)
                                        (a :->: x)
                                        (Int :->: x)
                                        (a :->: x)
  empty = PrologIdTrie Trie.empty Trie.empty Trie.empty Trie.empty
  lookup (InId k)  (PrologIdTrie i o u f) = Trie.lookup k i
  lookup (OutId k) (PrologIdTrie i o u f) = Trie.lookup k o
  lookup (UId k)   (PrologIdTrie i o u f) = Trie.lookup k u
  lookup (FunctorId k) (PrologIdTrie i o u f) = Trie.lookup k f
  insert (InId k)  v (PrologIdTrie i o u f) = PrologIdTrie (Trie.insert k v i) o u f
  insert (OutId k) v (PrologIdTrie i o u f) = PrologIdTrie i (Trie.insert k v o) u f
  insert (UId k)   v (PrologIdTrie i o u f) = PrologIdTrie i o (Trie.insert k v u) f
  insert (FunctorId k) v (PrologIdTrie i o u f) = PrologIdTrie i o u (Trie.insert k v f)
  toList (PrologIdTrie i o u f) = map (first InId)      (Trie.toList i) ++
                                  map (first OutId)     (Trie.toList o) ++
                                  map (first UId)       (Trie.toList u) ++
                                  map (first FunctorId) (Trie.toList f)

$(derive makeFunctor     ''PrologId)
$(derive makeFoldable    ''PrologId)
$(derive makeTraversable ''PrologId)
