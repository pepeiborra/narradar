{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narradar.Utils.Convert where

import Narradar.Types.ArgumentFiltering (AF_, mapSymbols)
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Labellings
import Narradar.Types.Term
import Narradar.Types.Var


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

-- Labellings
-- ----------
instance Convert id (Labelled id) where convert = Plain
instance Convert String LId       where convert = convert . (convert :: String -> Labelled String)
instance Convert LId    LId       where convert = id

-- Terms
-- ------
instance (Functor f, Convert v v') => Convert (Term f v) (Term f v') where convert = fmap convert
instance (Convert id id') => Convert (TermN id v) (TermN id' v) where convert = mapTermSymbols convert
instance Convert (TermN id v) (TermN id v) where convert = id

-- AFs
-- ---
instance (Convert id id', Ord id') => Convert (AF_ id) (AF_ id') where convert = mapSymbols convert


