{-# LANGUAGE TypeFamilies #-}

module Data.NarradarTrie (module Data.TrieFamily) where

import Data.ByteString (ByteString)
import qualified Data.Trie as BTrie
import Data.TrieFamily
import Prelude hiding (lookup)

{-
instance HasTrie Atom where
  newtype Atom :->: x = AtomTrie (Map Atom x)
  empty = AtomTrie mempty
  lookup k (AtomTrie m) = Map.lookup k m
  insert k v (AtomTrie m) = AtomTrie $ Map.insert k v m
  toList (AtomTrie m) = Map.toList m
-}
instance HasTrie ByteString where
  newtype ByteString :->: x = BSTrie (BTrie.Trie x)
  empty = BSTrie BTrie.empty
  lookup k (BSTrie m) = BTrie.lookup k m
  insert k v (BSTrie m) = BSTrie $ BTrie.insert k v m
  toList (BSTrie m) = BTrie.toList m

