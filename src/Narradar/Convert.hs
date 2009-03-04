{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Narradar.Convert where

import qualified Data.Set as Set

import Data.Foldable (toList)

import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.Utils
import TRS

-- ------------------
-- External interface
-- ------------------
mkTRS = tRS . fmap2 convert
class Convert f g where convert :: f -> g

-- -----------------
-- The Convert class
-- -----------------
{-# RULES "convert/id" forall x. convert x = x #-}

instance (Convert a a', Convert b b') => Convert (a,b) (a',b') where convert (a,b) = (convert a, convert b)
instance (Convert a b) => Convert [a] [b] where convert = map convert
instance (Convert b a) => Convert (a -> c) (b -> c) where convert = (. convert)
instance ConvertT f f' => Convert (Rule f) (Rule f') where convert = fmap convert

-- ConvertT short for Convert Term
-- -------------------------------
--instance (Convert f fg, Convert fg g) => Convert f g where convert = convert . (convert :: Term f -> Term fg)
class    (Functor f, Functor g, Convert (Term f) (Term g)) => ConvertT f g
instance (Functor f, Functor g, Convert (Term f) (Term g)) => ConvertT f g

-- DP Identifiers
-- --------------
instance Convert a (Identifier a) where convert = IdFunction
instance Convert a String => Convert (Identifier a) String where
    convert (IdDP a)       = convert a ++ "#"
    convert (IdFunction a) = convert a

instance Convert (Term Basic)  (Term Basic')   where convert = reinject
instance Convert (Term Basic)  (Term BasicId)  where convert = convertToId
instance Convert (Term Basic)  (Term BBasic)   where convert = reinject
instance Convert (Term Basic)  (Term BBasicId) where convert = convertToId
instance Convert (Term Basic') (Term BasicId)  where convert = convertToId
instance Convert (Term BBasic) (Term BBasicId) where convert = convertToId
instance Convert (Term f) (Term f) where convert = id

--convertToId :: (T String :<: f, T Identifier :<: f', HashConsed f') =>
convertToId = foldTerm convertToIdF

class    Functor f => ConvertToId f g  where convertToIdF :: f (Term g) -> Term g
instance Functor f => ConvertToId f f  where convertToIdF = In
instance (T (Identifier id) :<: g, HashConsed g) => ConvertToId (T id) g where convertToIdF (T f tt) = term (IdFunction f) tt
instance (a :<: g) =>      ConvertToId a g          where convertToIdF = inject
instance (ConvertToId a g, ConvertToId b g) => ConvertToId (a:+:b) g    where convertToIdF (Inl x) = convertToIdF x; convertToIdF (Inr x) = convertToIdF x

-- Identity instances. Annoying
-- ----------------------------
instance Convert Char Char where convert = id
instance Convert Int Int   where convert = id
instance Convert Bool Bool where convert = id
instance Convert Float Float where convert = id
instance Convert Id   Id   where convert = id
--instance Convert (Term Basic)    (Term Basic)      where convert = id
--instance Convert (Term BBasicId) (Term BBasicId)   where convert = id
--instance Convert (Term BBasicLId) (Term BBasicLId) where convert = id
--instance Convert (a,b) (a,b) where convert (a,b) = id

-- Incoherent instance
--instance Convert f f where convert = id

-- Prolog Identifiers
-- ------------------
instance Convert a String => Convert (PIdentifier a) String where
  convert (InId a)      = convert a ++ "_in"
  convert (OutId a)     = convert a ++ "_out"
  convert (UId i)       = "u_" ++ show i
  convert (FunctorId f) = convert f

instance Convert PS PS   where convert = id
instance Convert PId PId where convert = id

instance Convert (TRS.Term BasicPS)  (TRS.Term BasicPId) where convert = convertToId
instance Convert (TRS.Term BasicLPS) (TRS.Term BasicLPId) where convert = convertToId

-- Labellings
-- ----------
instance Convert id (Labelled id) where convert = Plain
instance Convert String LId       where convert = convert . (convert :: String -> Labelled String)
instance Convert PS     LPId      where convert = IdFunction . Plain
instance Convert PId    LPId      where convert = fmap Plain
instance Convert LId    LId       where convert = id
instance Convert LPId LPId where convert = id

--convertToLabelled :: (T id :<: f, T (Labelled id) :<: g) => Term f -> Term g
convertToLabelled = foldTerm convertToLF

class (Functor f, Functor g) =>  ConvertToL f g where convertToLF :: f(Term g) -> Term g
instance Functor f => ConvertToL f f where convertToLF = In
instance (T (Labelled (PIdentifier id)) :<: g) => ConvertToL (T (PIdentifier id)) g where
    convertToLF (T (InId f)  tt) = term (Labelling [1.. length tt] (InId f)) tt
    convertToLF (T (OutId f) tt) = term (Labelling [1.. length tt] (OutId f)) tt
    convertToLF (T f         tt) = term (Plain f) tt
instance (T (Labelled id) :<: g) => ConvertToL (T id) g where
    convertToLF (T f tt) = term (Plain f) tt
instance (Eq id, T (Identifier (Labelled id)) :<: g) => ConvertToL (T (Identifier id)) g where
    convertToLF (T f tt) = term (fmap Plain f) tt
instance (f :<: g) => ConvertToL f g where convertToLF = inject
instance (ConvertToL a g, ConvertToL b g) => ConvertToL (a:+:b) g where
  convertToLF (Inl x) = convertToLF x; convertToLF (Inr x) = convertToLF x


instance Convert (Term Basic)    (Term BasicLId)  where convert = convertToId . (convertToLabelled :: Term Basic -> Term BasicL)
instance Convert (Term BasicPS)  (Term BasicLPS)  where convert = convertToLabelled
instance Convert (Term BasicPId) (Term BasicLPId) where convert = convertToLabelled


-- TRSs
-- ----

instance (ConvertT f f', Ord id, Ord id', T id :<: f, T id' :<: f', TRSC f, TRSC f') => Convert (NarradarTRS id f) (NarradarTRS id' f') where
    {-# off SPECIALIZE instance Convert (NarradarTRS Id BBasicId)  (NarradarTRS LId BBasicLId) #-}
    {-# off SPECIALIZE instance Convert (NarradarTRS String Basic) (NarradarTRS LId BBasicLId) #-}
    {-# off SPECIALIZE instance Convert (NarradarTRS String Basic) (NarradarTRS Id BBasicId) #-}
    convert(PrologTRS rr sig) = prologTRS' (Set.mapMonotonic convert rr)
    convert (TRS rr _)        = narradarTRS (map convert$ toList rr :: [Rule f']) :: NarradarTRS id' f'
