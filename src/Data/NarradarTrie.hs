{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.NarradarTrie (module Trie) where

import Control.Arrow
import Data.AlaCarte
import Data.ByteString (ByteString)
import Data.Maybe
import qualified Data.Trie as BTrie
import Data.TrieFamily as Trie
import Language.Prolog.Representation as Prolog
import Text.PrettyPrint.HughesPJClass
import Prelude hiding (lookup)

instance (Pretty a, Pretty b, HasTrie a) => Pretty (a :->: b) where
 pPrint = pPrint . toList

{-
instance HasTrie Atom where
  newtype Atom :->: x = AtomTrie (Map Atom x)
  empty = AtomTrie mempty
  lookup k (AtomTrie m) = Map.lookup k m
  insert k v (AtomTrie m) = AtomTrie $ Map.insert k v m
  toList (AtomTrie m) = Map.toList m
-}

-- ByteStrings

instance HasTrie ByteString where
  newtype ByteString :->: x = BSTrie (BTrie.Trie x)
  empty = BSTrie BTrie.empty
  lookup = lookupBS
  insert k v (BSTrie m) = BSTrie $ BTrie.insert k v m
  toList (BSTrie m) = BTrie.toList m

{-# INLINE lookupBS #-}
lookupBS k (BSTrie m) = BTrie.lookup k m

-- A la Carte data types

instance (HasTrie (f (Expr f))) => HasTrie (Expr f) where
  newtype Expr f :->: x = ExprTrie (f(Expr f) :->: x)
  empty = ExprTrie Trie.empty
  lookup (In k) (ExprTrie m)   = Trie.lookup k m
  insert (In k) v (ExprTrie m) = ExprTrie $ insert k v (m)
  toList (ExprTrie m) = map (first In) $ Trie.toList m

instance (HasTrie (f a), HasTrie (g a)) => HasTrie ((f:+:g) a) where
  newtype ((f:+:g) a) :->: x = SumTrie ( Either (f a) (g a) :->: x)
  empty = SumTrie Trie.empty
  lookup = lookupSum
  insert (Inl l) v (SumTrie m) = SumTrie $ Trie.insert (Left l)  v m
  insert (Inr r) v (SumTrie m) = SumTrie $ Trie.insert (Right r) v m
  toList (SumTrie m) = map (first toSum) $ Trie.toList m

{-# INLINE lookupSum #-}
lookupSum (Inl l) (SumTrie m) = Trie.lookup (Left l)  m
lookupSum (Inr r) (SumTrie m) = Trie.lookup (Right r) m

toSum (Left l)  = Inl l
toSum (Right r) = Inr r


-- Prolog representation data types

instance HasTrie id => HasTrie (T id a) where
  newtype T id a :->: x = TTrie (id :->: x)
  empty = TTrie Trie.empty
  lookup (T k) (TTrie m)   = Trie.lookup k m
  insert (T k) v (TTrie m) = TTrie $ insert k v (m)
  toList (TTrie m) = map (first T) $ Trie.toList m

instance HasTrie id => HasTrie (K id a) where
  newtype K id a :->: x = KTrie (id :->: x)
  empty = KTrie Trie.empty
  lookup (K k) (KTrie m)   = Trie.lookup k m
  insert (K k) v (KTrie m) = KTrie $ insert k v (m)
  toList (KTrie m) = map (first K) $ Trie.toList m

instance HasTrie PrologP_ where
  data PrologP_ :->: x = PrologPTrie (Maybe x) (Maybe x) (Maybe x) (Maybe x)
  empty = PrologPTrie Nothing Nothing Nothing Nothing
  lookup Is (PrologPTrie is _ _ _) = is
  lookup Eq (PrologPTrie _ eq _ _) = eq
  lookup Cut (PrologPTrie _ _ cut _) = cut
  lookup Ifte (PrologPTrie _ _ _ ifte) = ifte
  insert Is v (PrologPTrie is eq cut ifte) = PrologPTrie (Just v) eq cut ifte
  insert Eq v (PrologPTrie is eq cut ifte) = PrologPTrie is (Just v) cut ifte
  insert Cut v (PrologPTrie is eq cut ifte) = PrologPTrie is eq (Just v) ifte
  insert Ifte v (PrologPTrie is eq cut ifte) = PrologPTrie is eq cut (Just v)
  toList (PrologPTrie is eq cut ifte) = catMaybes [ fmap (Is,) is
                                                  , fmap (Eq,) eq
                                                  , fmap (Cut,) cut
                                                  , fmap (Ifte,) ifte
                                                  ]

instance HasTrie PrologT_ where
  data PrologT_ :->: x = PrologTTrie (Maybe x) (Maybe x) (Maybe x) (Maybe x) (Maybe x) (String :->: x)
  empty = PrologTTrie Nothing Nothing Nothing Nothing Nothing Trie.empty
  lookup Zero (PrologTTrie is _ _ _ _ _) = is
  lookup Succ (PrologTTrie _ eq _ _ _ _) = eq
  lookup Tup (PrologTTrie _ _ cut _ _ _) = cut
  lookup Cons (PrologTTrie _ _ _ ifte _ _) = ifte
  lookup Nil (PrologTTrie _ _ _ _ nil _) = nil
  lookup (String k) (PrologTTrie _ _ _ _ _ s) = Trie.lookup k s
  insert Zero v (PrologTTrie is eq cut ifte nil s) = PrologTTrie (Just v) eq cut ifte nil s
  insert Succ v (PrologTTrie is eq cut ifte nil s) = PrologTTrie is (Just v) cut ifte nil s
  insert Tup v (PrologTTrie is eq cut ifte nil s)  = PrologTTrie is eq (Just v) ifte nil s
  insert Cons v (PrologTTrie is eq cut ifte nil s) = PrologTTrie is eq cut (Just v) nil s
  insert Nil v (PrologTTrie is eq cut ifte nil s)  = PrologTTrie is eq cut ifte (Just v) s
  insert (String k) v (PrologTTrie is eq cut ifte nil s) = PrologTTrie is eq cut ifte nil (Trie.insert k v s)
  toList (PrologTTrie is eq cut ifte nil s)
      = catMaybes [ fmap (Zero,) is
                  , fmap (Succ,) eq
                  , fmap (Tup,) cut
                  , fmap (Cons,) ifte
                  , fmap (Nil,) nil
                  ] ++
        map (first String) (Trie.toList s)
