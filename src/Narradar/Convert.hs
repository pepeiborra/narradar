{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narradar.Convert where

import qualified Data.Set as Set

import Data.Foldable (toList)

import Narradar.ArgumentFiltering (AF_, mapSymbols)
import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.Utils
import Narradar.Term
import Narradar.Var

import Data.Term
import Data.Term.Rules

-- ------------------
-- External interface
-- ------------------
class Convert f g where convert :: f -> g

-- -----------------
-- The Convert class
-- -----------------
{-# RULES "convert/id" forall x. convert x = x #-}

instance (Convert a a', Convert b b') => Convert (a,b) (a',b') where convert (a,b) = (convert a, convert b)
instance (Convert a b) => Convert [a] [b] where convert = map convert
instance (Convert b a) => Convert (a -> c) (b -> c) where convert = (. convert)
instance Convert (Term t v) (Term t' v') => Convert (Rule t v) (Rule t' v') where convert = fmap convert

-- DP Identifiers
-- --------------
instance Convert a (Identifier a) where convert = IdFunction
instance Convert a String => Convert (Identifier a) String where
    convert (IdDP a)       = convert a ++ "#"
    convert (IdFunction a) = convert a

-- Identity instances. Annoying
-- ----------------------------
instance Convert Char Char where convert = id
instance Convert Int Int   where convert = id
instance Convert Bool Bool where convert = id
instance Convert Float Float where convert = id
instance Convert Id   Id   where convert = id
instance Convert Var Var   where convert = id

-- Incoherent instance
--instance Convert f f where convert = id

-- Prolog Identifiers
-- ------------------
instance Convert a String => Convert (PrologId a) String where
  convert (InId a)      = convert a ++ "_in"
  convert (OutId a)     = convert a ++ "_out"
  convert (UId i)       = "u_" ++ show i
  convert (FunctorId f) = convert f

instance Convert PS PS   where convert = id
instance Convert PId PId where convert = id

-- Labellings
-- ----------
instance Convert id (Labelled id) where convert = Plain
instance Convert String LId       where convert = convert . (convert :: String -> Labelled String)
instance Convert PS     LPId      where convert = IdFunction . Plain
instance Convert PId    LPId      where convert = fmap Plain
instance Convert LId    LId       where convert = id
instance Convert LPId LPId where convert = id

-- Terms
-- ------
instance (Functor f, Convert v v') => Convert (Term f v) (Term f v') where convert = fmap convert
instance (Convert id id') => Convert (TermN id v) (TermN id' v) where convert = mapTermId convert
instance Convert (TermN id v) (TermN id v) where convert = id

convertToLabelled :: IsPrologId id => TermN id v -> TermN (Labelled id) v
convertToLabelled = foldTerm return f where
  f (Term id  tt)
    | isInId id || isOutId id = term (Labelling [1..length tt] id) tt
    | otherwise               = term (Plain id) tt

instance Convert (TermN PS     v) (TermN LPS  v) where convert = convertToLabelled


-- AFs
-- ---
instance (Convert id id', Ord id') => Convert (AF_ id) (AF_ id') where convert = mapSymbols convert


