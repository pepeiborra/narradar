{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Term
                     (TermF(..), ArityId(..), HasArity(..), StringId, DPIdentifier(..)
                     ,TermN, RuleN, constant, term, term1
                     ,termIds, Size(..), fromSimple
                     ,ExtraVars(..)
                     ,Substitution, SubstitutionNF, GetVarsObservable
                     ,module Narradar.Constraints.Unify
                     ,module Data.Term
                     ,Free(..)
                     ,MonadFree(..))
    where

import           Control.Applicative
import           Control.Applicative.Compose
import           Control.Arrow          (first)
import           Control.DeepSeq
import           Control.DeepSeq.Extras
import           Control.Monad.ConstrainedNormal (NF)
import           Control.Monad.Free
import           Data.Char
import           Data.Bifunctor
import           Data.ByteString.Char8  as BS (ByteString, pack, unpack)
import           Data.Constraint        ( (:-)(..), Dict(..))
import           Data.Foldable          as F (Foldable(..),sum,msum)
import           Data.Hashable
import qualified Data.Map               as Map
import qualified Data.Set               as Set
import           Data.Traversable
import           Data.Typeable
import           Prelude.Extras

import           Data.Term
                  (Term, TermFor, evalTerm, foldTerm, foldTermM
                  ,Match(..)
                  ,HasId(..), HasId1(..), MapId(..), mapTermSymbols, mapRootSymbol, collect
                  ,MonadVariant(..), evalMEnv, execMEnv
                  ,Position, positions, occurrences, (!), updateAt
                  ,WithNote(..), WithNote1(..), annotateWithPos, noteV, note, dropNote
                  ,find', varBind, occursIn
                  ,isVar, isLinear, Rename(..)
                  ,rootSymbol, subterms, directSubterms, properSubterms
                  )
import qualified Data.Term.Simple       as Simple
import qualified Data.Id.Family         as Family
import qualified Data.Term.Family       as Family
import qualified Data.Rule.Family       as Family
import qualified Data.Var.Family        as Family

import           Narradar.Constraints.Unify hiding (TermF, Var)
import           Narradar.Framework.Ppr
import           Narradar.Types.Var

import           GHC.Generics          (Generic,Generic1)
import           Debug.Hoed.Observe

-- ---------------------
-- Basic Identifiers
-- ---------------------
type StringId = ArityId ByteString
data ArityId a = ArityId {the_id :: a, the_arity::Int} deriving (Eq, Ord, Show, Typeable, Generic,Generic1)

instance Pretty StringId where pPrint ArityId{..} = text (BS.unpack the_id)
instance Pretty a => Pretty (ArityId a) where pPrint ArityId{..} = pPrint the_id

class    HasArity id where getIdArity :: id -> Int
instance HasArity (ArityId a) where getIdArity = the_arity

-- -----------------------
-- Concrete DP Identifiers
-- -----------------------
data DPIdentifier a = IdFunction a | IdDP a | AnyIdentifier
                    deriving (Ord, Typeable, Functor, Foldable, Traversable, Generic,Generic1)

instance Eq a => Eq (DPIdentifier a) where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False


-- -------
-- Terms
-- -------

data TermF id f = Term id [f] deriving (Eq,Ord,Show,Generic,Generic1,Typeable)
type TermN id = Term (TermF id) Var
type RuleN id = RuleF(TermN id)

instance Eq id => Eq1 (TermF id) where (==#) = (==)
instance Ord id => Ord1 (TermF id) where compare1 = compare
instance Show id => Show1 (TermF id) where showsPrec1 = showsPrec

type instance Family.Id (TermF id) = id
type instance Family.Id (Term f v) = Family.Id f
type instance Family.TermF (TermF id f) = TermF id

instance Eq id => Applicative (Maybe :+: TermF id) where
  pure _ = Compose Nothing
  Compose(Just(Term id1 ff)) <*> Compose(Just(Term id2 xx))
    | id1 == id2 = Compose(Just(Term id1 (zipWith ($) ff xx)))
    | otherwise  = Compose Nothing

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

-- | Extra Variables are variables which occur in the right side of a rule but not in the left side
class ExtraVars thing where extraVars :: thing -> [Family.Var thing]
instance (Ord (Family.Var trs), Functor (TermF trs), Foldable (TermF trs), HasRules trs, ExtraVars(Family.Rule trs), Family.Var trs ~ Family.Var (Family.Rule trs)) => ExtraVars trs where
    extraVars = concatMap extraVars . rules
instance (GetVars a, Ord(Family.Var a)) => ExtraVars (RuleF a) where
    extraVars (l:->r) =
      Set.toList (getVars r `Set.difference` getVars l)


-- Specific instance for TermF, only for efficiency
instance Eq id => Unify (TermF id) where
  {-# SPECIALIZE instance Unify (TermF String) #-}
  {-# SPECIALIZE instance Unify (TermF StringId) #-}
  {-# SPECIALIZE instance Unify (TermF (DPIdentifier StringId)) #-}
  unifyM = unifyF where
   unifyF t s = do
    t' <- find' t
    s' <- find' s
    case (t', s') of
      (Pure vt, Pure vs) -> when(vt /= vs) $ varBind vt s'
      (Pure vt, _)  -> vt `occursIn` s' >>= \occ -> if occ then fail "occurs" else varBind vt s'
      (_, Pure vs)  -> vs `occursIn` t' >>= \occ -> if occ then fail "occurs" else varBind vs t'
      (Impure (Term f1 []), Impure (Term f2 [])) -> if f1 == f2 then return () else fail "structure mismatch"
      (Impure (Term f1 [x]), Impure (Term f2 [y])) -> if f1 == f2 then unifyF x y else fail "structure mismatch"
      (Impure (Term f1 tt1), Impure (Term f2 tt2)) 
           | f1 == f2  -> zipWithM_ unifyF tt1 tt2
           | otherwise -> fail "structure mismatch"

instance Ord id => HasId1 (TermF id) where
    getId1 (Term id _) = Just id
    fromId1 id = Term id []

instance MapId TermF where mapIdM f (Term id tt) = (`Term` tt) <$> f id

-- -----
-- Size
-- -----
class Size t where size :: t -> Int
instance (Functor f, Foldable f) => Size (Term f v) where
  size = foldTerm (const 1) (\f -> 1 + F.sum f)
instance Size t  => Size [t] where size = F.sum . fmap size
instance (Size a) => Size (RuleF a) where size = F.sum . fmap size

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
-- -------
-- Hashing
-- -------
instance (Hashable id, Hashable a) => Hashable (TermF id a) where
  hashWithSalt s (Term id tt) =
    Prelude.foldr (hashWithSalt) (hashWithSalt s id) (map (hashWithSalt s) tt)

instance (Functor f, Hashable a, Hashable (f Int)) => Hashable (Free f a) where
  hashWithSalt s = foldFree (hashWithSalt s) (hashWithSalt s)

instance Hashable a => Hashable (ArityId a) where hashWithSalt s (ArityId id a)  = hashWithSalt a (hashWithSalt s id)

-- ----------------
-- NFData instances
-- ----------------

instance NFData Var where
  rnf (Var s i) = rnf s `seq` rnf i `seq` ()

instance (NFData id) => NFData1 (TermF id) where
  rnf1 (Term i tt) = rnf i `seq` rnf tt

instance NFData1 ArityId where
  rnf1 (ArityId a i) = rnf i `seq` rnf a `seq` ()

instance NFData a => NFData(ArityId a) where rnf = rnf1

-- --------------------
-- Observable instances
-- --------------------
instance Observable id => Observable1 (TermF id) where observer1 (Term id tt) = send "" (return Term << id .<< tt)
instance (Observable a, Observable id) => Observable (TermF id a) where
  observer = observer1 ; observers = observers1

instance Observable1 ArityId
instance Observable a => Observable (ArityId a) where
  observer = observer1 ; observers = observers1

--instance (Pretty(TermN id)) => Observable (TermN id) where observer t = t `seq` send (show$ pPrint t) (return t)
