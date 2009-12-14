{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards #-}

module Narradar.Types.Term
                     (TermF(..), ArityId(..), HasArity(..), StringId
                     ,TermN, RuleN, constant, term, term1
                     ,termIds, Size(..), fromSimple
                     ,ExtraVars(..)
                     ,module Data.Term, module Data.Term.Rules, MonadFree(..))
    where

import Control.Arrow (first)
import Control.DeepSeq
import Control.Monad.Free
import Data.Char
import Data.Bifunctor
import Data.ByteString.Char8 as BS (ByteString, pack, unpack)
import Data.Foldable as F (Foldable(..),sum,msum)
import Data.NarradarTrie (HasTrie, (:->:))
import qualified Data.NarradarTrie as Trie
import qualified Data.Set as Set
import Data.Traversable
import Data.Term hiding (unify, unifies, applySubst, find)
import qualified Data.Term.Simple as Simple
import Data.Term.Rules hiding (unifies', matches')
import Data.Typeable

import qualified Data.Map as Map

import Narradar.Framework.Ppr
import Narradar.Types.Var

-- ---------------------
-- Basic Identifiers
-- ---------------------
type StringId = ArityId ByteString
data ArityId a = ArityId {the_id :: a, the_arity::Int} deriving (Eq, Ord, Show, Typeable)

instance Pretty StringId where pPrint ArityId{..} = text (BS.unpack the_id)
instance Pretty a => Pretty (ArityId a) where pPrint ArityId{..} = pPrint the_id

class    HasArity id where getIdArity :: id -> Int
instance HasArity (ArityId a) where getIdArity = the_arity

-- -------
-- Terms
-- -------

data TermF id f = Term id [f] deriving (Eq,Ord,Show)
type TermN id = Term (TermF id) Var
type RuleN id = RuleF(TermN id)

term :: id -> [Term (TermF id) a] -> Term (TermF id) a
term f = Impure . Term f

term1 f t = Impure (Term f [t])

constant :: id -> Term (TermF id) a
constant f = term f []

termIds :: MonadPlus m => Term (TermF id) a -> m id
termIds = foldTerm (const mzero) f where
    f (Term f tt) = return f `mplus` F.msum tt


fromSimple :: Simple.TermF String a -> TermF StringId a
fromSimple (Simple.Term id tt) = Term (ArityId (BS.pack id) (length tt)) tt

fromSimple' :: Simple.TermF id a -> TermF (ArityId id) a
fromSimple' (Simple.Term id tt) = Term (ArityId id (length tt)) tt


class    ExtraVars v thing | thing -> v where extraVars :: thing -> [v]
instance (Ord v, Functor t, Foldable t, HasRules t v trs) => ExtraVars v trs where
    extraVars = concatMap extraVars . rules

instance (Ord v, Functor t, Foldable t) => ExtraVars v (Rule t v) where
    extraVars (l:->r) = Set.toList (Set.fromList(vars r) `Set.difference` Set.fromList(vars l))


-- Specific instance for TermF, only for efficiency
instance Eq id => Unify (TermF id) where
  {-# SPECIALIZE instance Unify (TermF String) #-}
  unifyM = unifyF where
   unifyF t s = do
    t' <- find' t
    s' <- find' s
    case (t', s') of
      (Pure vt, Pure vs) -> when(vt /= vs) $ varBind vt s'
      (Pure vt, _)  -> vt `occursIn` s' >>= \occ -> if occ then fail "occurs" else varBind vt s'
      (_, Pure vs)  -> vs `occursIn` t' >>= \occ -> if occ then fail "occurs" else varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
                                           | otherwise = fail "structure mismatch"

instance Ord id =>  HasId (TermF id) where
    type TermId (TermF id) = id
    getId (Term id _) = Just id

instance MapId TermF where mapIdM f (Term id tt) = (`Term` tt) `liftM` f id

-- -----
-- Size
-- -----
class Size t where size :: t -> Int
instance (Functor f, Foldable f) => Size (Term f v) where
  size = foldTerm (const 1) (\f -> 1 + F.sum f)
instance Size t  => Size [t] where size = F.sum . fmap size
instance (Functor f, Foldable f) => Size (Rule f v) where size = F.sum . fmap size

-- Functor boilerplate
-- --------------------
instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
instance Foldable (TermF id) where
    foldMap  f (Term _ tt) = foldMap f tt
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a `fmap` traverse f tt

instance Bifunctor TermF where bimap f g (Term a tt) = Term (f a) (map g tt)

-- Pretty
-- ---

-- I believe the sole purpose of this instance is now to force late instance resolution of
-- Pretty constraints on (Term t v).
-- In absence of this instance there is no overlapping and GHC eagerly chooses the instance
-- in Data.Term.Ppr, flattening it to the constraints and Pretty v and Pretty (t(Term t v)).
-- This is undesirable since Pretty (Term t v) is more compact and declarative
{-
instance Pretty id => Pretty (TermN id) where
 pPrint (Pure a)   = pPrint a
 pPrint (Impure t) = pPrintT t
  where
    pPrintT (Term n []) = pPrint n
    pPrintT (Term n [x,y]) | not (any isAlpha $ show $ pPrint n) = pPrint x <+> pPrint n <+> pPrint y
    pPrintT (Term n tt) = pPrint n <> parens (hcat$ punctuate comma$ map pPrint tt)

instance Pretty (TermN String) where
 pPrint (Pure a)   = pPrint a
 pPrint (Impure t) = pPrintT t
  where
    pPrintT (Term n []) = text n
    pPrintT (Term n [x,y]) | not (any isAlpha n) = pPrint x <+> text n <+> pPrint y
    pPrintT (Term n tt) = text n <> parens (hcat$ punctuate comma$ map pPrint tt)
-}

instance (Pretty a, Pretty id) => Pretty (TermF id a) where
    pPrint (Term n []) = pPrint n
    pPrint (Term n [x,y]) | not (any isAlpha $ show $ pPrint n) = pPrint x <+> pPrint n <+> pPrint y
    pPrint (Term n tt) = pPrint n <> parens (hcat$ punctuate comma$ map pPrint tt)
{-
instance Pretty a => Pretty (TermF String a) where
    pPrint (Term n []) = text n
    pPrint (Term n [x,y]) | not (any isAlpha n) = pPrint x <+> text n <+> pPrint y
    pPrint (Term n tt) = text n <> parens (hcat$ punctuate comma $ map pPrint tt)
-}
-- -------------------
-- Trie instances
-- -------------------

instance (HasTrie a, HasTrie (f (Free f a))) => HasTrie (Free f a) where
  data Free f a :->: x = FreeTrie !(a :->: x) !(f (Free f a) :->: x)
  empty = FreeTrie Trie.empty Trie.empty
  lookup (Pure k) (FreeTrie pt it) = Trie.lookup k pt
  lookup (Impure k) (FreeTrie pt it) = Trie.lookup k it
  insert (Pure k) v (FreeTrie pt it) = FreeTrie (Trie.insert k v pt) it
  insert (Impure k) v (FreeTrie pt it) = FreeTrie pt (Trie.insert k v it)
  toList (FreeTrie pt it) = map (first Pure)   (Trie.toList pt) ++
                            map (first Impure) (Trie.toList it)

instance (HasTrie id, HasTrie a) => HasTrie (TermF id a) where
  newtype TermF id a :->: x = TermTrie ((id, [a]) :->: x)
  empty = TermTrie Trie.empty
  lookup (Term id tt) (TermTrie m) = Trie.lookup (id,tt) m
  insert (Term id tt) v (TermTrie m) = TermTrie $ Trie.insert (id,tt) v m
  toList (TermTrie m) = map (first (uncurry Term)) (Trie.toList m)
{-
instance HasTrie id => HasTrie (TermN id) where
  data TermN id :->: x = TermNTrie !(Var :->: x) !( (id,[TermN id]) :->: x)
  empty = TermNTrie Trie.empty Trie.empty
  lookup (Impure(Term id tt)) (TermNTrie vt mt) = Trie.lookup (id,tt) mt
  lookup (Pure v) (TermNTrie vt _) = Trie.lookup v vt
  insert (Impure(Term id tt)) v (TermNTrie vt mt) = TermNTrie vt $ Trie.insert (id,tt) v mt
  insert (Pure v) x (TermNTrie vt mt) = TermNTrie (Trie.insert v x vt) mt
  toList (TermNTrie vt mt) = map (first (uncurry term)) (Trie.toList mt) ++
                             map (first return) (Trie.toList vt)
-}
instance HasTrie a => HasTrie (ArityId a) where
  newtype ArityId a :->: x = ArityIdTrie ((a,Int) :->: x)
  empty = ArityIdTrie Trie.empty
  lookup (ArityId a i) (ArityIdTrie m) = Trie.lookup (a,i) m
  insert (ArityId a i) v (ArityIdTrie m) = ArityIdTrie $ Trie.insert (a,i) v m
  toList (ArityIdTrie m) = map (first (uncurry ArityId)) (Trie.toList m)

instance HasTrie Var where
  newtype Var :->: x = VarTrie (Int :->: (Maybe String, x))
  empty = VarTrie Trie.empty
  lookup (Var s i) (VarTrie m) = fmap snd $ Trie.lookup i m
  insert (Var s i) v (VarTrie m) = VarTrie $ Trie.insert i (s,v) m
  toList (VarTrie m) = [(Var s i, v) | (i, (s,v)) <- Trie.toList m]


-- ----------------
-- NFData instances
-- ----------------

instance NFData Var where
  rnf (Var s i) = rnf s `seq` rnf i `seq` ()

instance (NFData a, NFData id) => NFData (TermF id a) where
  rnf (Term id tt) = rnf id `seq` rnf tt `seq` ()

instance NFData a => NFData (RuleF a) where
  rnf (a :-> b) = rnf a `seq` rnf b `seq` ()

instance NFData id => NFData (Signature id) where
  rnf (Sig cc dd) = rnf cc `seq` rnf dd `seq` ()

instance NFData id => NFData (ArityId id) where
  rnf (ArityId a i) = rnf i `seq` rnf a `seq` ()