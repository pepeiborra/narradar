{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}


module Identifiers where

import Control.Applicative
import Control.Arrow
import Data.HashTable (hashString)
import Data.Foldable (toList, Foldable)
import Data.Int
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import Language.Prolog.Syntax (Atom)
import Prelude

import TRS.Utils
import TRS
import Bottom

type Id = Identifier
type LId = Labelled Identifier

-- -----------------------
-- Named Term Signatures
-- -----------------------

type Basic'   = Var :+: T String :+: Hole
type BBasic   = Var :+: T String :+: Hole :+: Bottom
type BasicId  = Var :+: T Identifier :+: Hole
type BBasicId = Var :+: T Identifier :+: Hole :+: Bottom
type BBasicLId= Var :+: T (Labelled Identifier) :+: Hole :+: Bottom
instance HashConsed BBasicLId
instance HashConsed BBasicId
instance HashConsed BasicId
instance HashConsed BBasic
instance HashConsed Basic'
instance HashConsed (T Identifier)

-- ------------
-- DP Symbols
-- ------------
class (Show id, Ord id) => DPSymbol id where
  markDPSymbol, unmarkDPSymbol :: id -> id
  functionSymbol, dpSymbol :: String -> id
  isDP   :: id -> Bool
  isDP s = markDPSymbol s == s
  symbol :: id -> String

instance DPSymbol Identifier where
  markDPSymbol (IdFunction f) = IdDP f
  markDPSymbol f = f
  unmarkDPSymbol (IdDP n) = IdFunction n
  unmarkDPSymbol n = n
  functionSymbol = IdFunction; dpSymbol = IdDP
  symbol (IdFunction f) = f; symbol(IdDP f) = f

class (TRSC f, T id :<: f, DPSymbol id) =>DPMark f id | f -> id where
    markDP, unmarkDP :: Term f -> Term f
    markDP t | Just (T (n::id) tt) <- open t = term (markDPSymbol n) tt
             | otherwise = t
    unmarkDP t | Just (T (n::id) tt) <- open t = term (unmarkDPSymbol n) tt
               | otherwise = t

instance DPMark BasicId Identifier
instance DPMark BBasicId Identifier
instance DPMark BBasicLId (Labelled Identifier)

unmarkDPRule, markDPRule :: DPMark f id => Rule f -> Rule f
markDPRule   = fmap   markDP
unmarkDPRule = fmap unmarkDP

-- -----------------------
-- Concrete DP Identifiers
-- -----------------------

data Identifier = IdFunction String | IdDP String | AnyIdentifier deriving (Ord)
instance Eq Identifier where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False

instance Show Identifier where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

-- ---------
-- Convert
-- ---------

--mkTRS :: [Rule Basic] -> TRS Identifier BasicId
mkTRS = tRS . fmap2 convert

--convertToId :: (T String :<: f, T Identifier :<: f', HashConsed f') => 
convertToId = foldTerm convertToIdF

class    (T Identifier :<: g, Functor f) =>    ConvertToId f g          where convertToIdF :: f (Term g) -> Term g
instance (T Identifier :<: f) =>               ConvertToId f f          where convertToIdF = In
instance (T Identifier :<: g, HashConsed g) => ConvertToId (T String) g where convertToIdF (T f tt) = term (IdFunction f) tt
instance (a :<: g, T Identifier :<: g) =>      ConvertToId a g          where convertToIdF = inject
instance (ConvertToId a g, ConvertToId b g) => ConvertToId (a:+:b) g    where convertToIdF (Inl x) = convertToIdF x; convertToIdF (Inr x) = convertToIdF x

class    Convert f g where convert :: f -> g
{-# RULES "convert/id" forall x. convert x = x #-}

instance (Convert a a', Convert b b') => Convert (a,b) (a',b') where convert (a,b) = (convert a, convert b)
instance (Convert a b) => Convert [a] [b] where convert = map convert
--instance Convert (a,b) (a,b) where convert (a,b) = id
instance (Convert b a) => Convert (a -> c) (b -> c) where convert = (. convert)
instance ConvertT f f' => Convert (Rule f) (Rule f') where convert = fmap convert

instance Convert String Identifier where convert = IdFunction

-- Incoherent instance
--instance Convert f f where convert = id

--instance (Convert f fg, Convert fg g) => Convert f g where convert = convert . (convert :: Term f -> Term fg)
class (Functor f, Functor g, Convert (Term f) (Term g)) => ConvertT f g
instance (Functor f, Functor g, Convert (Term f) (Term g)) => ConvertT f g

instance Convert (Term Basic)  (Term Basic')   where convert = reinject
instance Convert (Term Basic)  (Term BasicId)  where convert = convertToId
instance Convert (Term Basic)  (Term BBasic)   where convert = reinject
instance Convert (Term Basic)  (Term BBasicId) where convert = convertToId
instance Convert (Term Basic') (Term BasicId)  where convert = convertToId
instance Convert (Term BBasic) (Term BBasicId) where convert = convertToId

-- Identity instances. Annoying
instance Convert Char Char where convert = id
instance Convert Int Int   where convert = id
instance Convert Bool Bool where convert = id
instance Convert Float Float where convert = id
instance Convert Identifier      Identifier        where convert = id
instance Convert LId             LId               where convert = id
instance Convert (Term Basic)    (Term Basic)      where convert = id
instance Convert (Term BBasicId) (Term BBasicId)   where convert = id
instance Convert (Term BBasicLId) (Term BBasicLId) where convert = id


hashId :: Show a => a -> Int32
hashId = hashString . show

instance HashTerm (T Identifier) where hashF (T id tt) = 14 * sum tt * hashId id

-- -----------
-- Labellings
-- -----------

data Labelled a = Labelling {labelling::[Int], unlabel::a} | Plain {unlabel::a} deriving (Eq,Ord)

instance Show a => Show (Labelled a) where
    show (Labelling l a) = show a ++ "_" ++ (concatMap show l)
    show (Plain a)       = show a
instance HashTerm (T (Labelled Identifier)) where
    hashF (T id tt)      = 15 * sum tt * hashId id

instance DPSymbol id => DPSymbol (Labelled id) where
    markDPSymbol   (Labelling l id) = Labelling l (markDPSymbol id);   markDPSymbol   (Plain f) = Plain$ markDPSymbol f
    unmarkDPSymbol (Labelling l id) = Labelling l (unmarkDPSymbol id); unmarkDPSymbol (Plain f) = Plain$ unmarkDPSymbol f
    functionSymbol = Plain . functionSymbol
    dpSymbol       = Plain . dpSymbol
    symbol (Plain f) = symbol f; symbol (Labelling _ f) = symbol f

instance Convert id (Labelled id) where convert = Plain
instance Convert String LId where convert = convert . (convert :: String -> Identifier)

--labelWith (open -> Just (T (id::Identifier) tt)) labelling = term (Labelling labelling id) tt
--labelWith :: Term BBasicId -> [Int] -> Term BBasicLId -- (LabelledVersionOf f)
--labelWith :: forall f f' id. (ConvertT f f', T (Labelled id) :<: f', Var :<: f, HashConsed f, HashConsed f') => Term f -> [Int] -> Term f'
labelWith t | _ <- t `asTypeOf` x = setLabel (convert t)

mapLabel f _  (Labelling ll i) = Labelling (f ll) i
mapLabel f l0 (Plain i)        = Labelling l0 i


mapLabelT f l0 = mapTerm (mapLabelTF f l0)

class MapLabelT' f f => MapLabelT f; instance MapLabelT' f f => MapLabelT f
class (f :<: g) => MapLabelT' f g where mapLabelTF :: ([Int] -> [Int]) -> [Int] -> f (Term g) -> Term g

instance (T (Labelled id) :<: g) => MapLabelT' (T (Labelled id)) g where mapLabelTF f l0 (T id tt) = inject (T (mapLabel f l0 id) tt)
instance (MapLabelT' f g, MapLabelT' f' g, (f:+:f') :<: g) => MapLabelT' (f :+: f') g where
    mapLabelTF f l0 (Inr x) = mapLabelTF f l0 x; mapLabelTF f l0 (Inl x) = mapLabelTF f l0 x
instance (f :<: g) => MapLabelT' f g where mapLabelTF _ _ = inject

--setLabel,appendLabel :: forall f id. (T (Labelled id) :<: f, HashConsed f) => Term f -> [Int] -> Term f
setLabel t ll = mapLabelT (const ll) ll t
appendLabel t ll = mapLabelT (++ ll) ll t

setLabelling (Labelling ll i) ll' = Labelling ll' i
setLabelling (Plain i)        ll' = Labelling ll' i
extendLabelling (Labelling ll i) ll' = Labelling (ll ++ ll') i
extendLabelling (Plain i)        ll' = Labelling ll' i

--convertToLabelled :: (T id :<: f, T (Labelled id) :<: g) => Term f -> Term g
convertToLabelled = foldTerm convertToLF

class (T (Labelled id) :<: g) =>  ConvertToL id f g | f g -> id where convertToLF :: f(Term g) -> Term g
instance (T (Labelled id) :<: f) => ConvertToL id f f where convertToLF = In
instance (T (Labelled id) :<: g, HashConsed g) => ConvertToL id (T id) g where convertToLF (T f tt) = term (Plain f) tt
instance (a :<: g, T (Labelled id) :<: g) => ConvertToL id a g where convertToLF = inject
instance (ConvertToL id a g, ConvertToL id b g) => ConvertToL id (a:+:b) g where
  convertToLF (Inl x) = convertToLF x; convertToLF (Inr x) = convertToLF x

instance Convert (Term BBasicId) (Term BBasicLId) where convert = convertToLabelled
instance Convert (Term Basic)    (Term BBasicLId) where convert = (convertToLabelled :: Term BBasicId -> Term BBasicLId) . convertToId
--instance (f' ~ LabelledVersionOf f) => Convert f f' where convert = convertToLabelled

type family   LabelledVersionOf (f :: * -> *) :: * -> *
type instance LabelledVersionOf (T id)    = T (Labelled id)
type instance LabelledVersionOf Var       = Var
type instance LabelledVersionOf (a :+: b) = (LabelledVersionOf a :+: LabelledVersionOf b)
type instance LabelledVersionOf Bottom    = Bottom
type instance LabelledVersionOf Hole      = Hole

--instance (f' ~ LabelledVersionOf f, DPMark f id) => DPMark f' (Labelled id) where


-- --------------------
-- TRSs in our setting
-- --------------------

data NarradarTRS id f where
    TRS :: (Ord id, TRSC f, T id :<: f) => Set (Rule f) -> Signature id -> NarradarTRS id f
    PrologTRS :: (Ord id, TRSC f, T id :<: f) => Set (Atom, Rule f) -> Signature id -> NarradarTRS id f

instance (Ord id, Ord (Term f), DPMark f id) => Ord (NarradarTRS id f) where
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BasicId) #-}
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BBasicId) #-}
    {-# SPECIALIZE instance Ord(NarradarTRS LId BBasicLId) #-}
    compare TRS{} PrologTRS{} = LT
    compare PrologTRS{} TRS{} = GT
    compare (TRS rr1 _) (TRS rr2 _)             = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2

instance (Ord id, T id :<: f, TRSC f) => TRS (NarradarTRS id f) id f where
    {-# SPECIALIZE instance TRS(NarradarTRS Id BasicId) Id BasicId #-}
    {-# SPECIALIZE instance TRS(NarradarTRS Id BBasicId) Id BBasicId #-}
    {-# SPECIALIZE instance TRS(NarradarTRS LId BBasicLId) LId BBasicLId #-}
    rules(TRS rr _)       = toList rr
    rules(PrologTRS rr _) = map snd (toList rr)
    tRS = narradarTRS

{-# SPECIALIZE narradarTRS ::  [Rule BBasicId] -> NarradarTRS Id BBasicId #-}
narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)

instance Ord id => SignatureC (NarradarTRS id f) id where
    {-# SPECIALIZE instance SignatureC(NarradarTRS Id BasicId) Id #-}
    {-# SPECIALIZE instance SignatureC(NarradarTRS Id BBasicId) Id #-}
    {-# SPECIALIZE instance SignatureC(NarradarTRS LId BBasicLId) LId #-}
    getSignature (TRS _ sig)       = sig
    getSignature (PrologTRS _ sig) = sig


instance (T id :<: f, Ord id, TRSC f) => Monoid (NarradarTRS id f) where
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BasicId) #-}
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BBasicId) #-}
    {-# SPECIALIZE instance Monoid(NarradarTRS LId BBasicLId) #-}
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature (snd <$> toList rr))
    mappend emptytrs trs | null (rules emptytrs) = trs
    mappend trs emptytrs | null (rules emptytrs) = trs

    mappend x y = error "error: are you sure you want to mappend different kinds of TRSs?" `const` x `const` y

instance (ConvertT f f', Ord id, Ord id', T id :<: f, T id' :<: f', TRSC f, TRSC f') => Convert (NarradarTRS id f) (NarradarTRS id' f') where
    {-# SPECIALIZE instance Convert (NarradarTRS Id BBasicId)  (NarradarTRS LId BBasicLId) #-}
    {-# SPECIALIZE instance Convert (NarradarTRS String Basic) (NarradarTRS LId BBasicLId) #-}
    {-# SPECIALIZE instance Convert (NarradarTRS String Basic) (NarradarTRS Id BBasicId) #-}
    convert(PrologTRS rr sig) = prologTRS' (Set.mapMonotonic convert rr)
    convert (TRS rr _)        = narradarTRS (map convert$ toList rr :: [Rule f']) :: NarradarTRS id' f'

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS :: forall id f. (Ord id, TRSC f, T id :<: f) => [(Atom, Rule f)] -> NarradarTRS id f
prologTRS rr = prologTRS' (Set.fromList rr)

prologTRS' :: forall id f. (Ord id, TRSC f, T id :<: f) => Set(Atom, Rule f) -> NarradarTRS id f
prologTRS' rr = PrologTRS rr (getSignature (snd <$> toList rr))



-- -------------------
-- Failed attempts
-- -------------------
{-
convert = foldTerm convertF

class (Functor f, TRSC g) => Convert f g where convertF :: f (Term g) -> Term g
instance TRSC f => Convert f f where convertF = In
instance (T Identifier :<: g, TRSC g) => Convert (T String) g where
    convertF (T f tt) = term (IdFunction f) tt
instance (Convert f1 g, Convert f2 g) => Convert (f1 :+: f2) g where
    convertF (Inl x) = convertF x
    convertF (Inr x) = convertF x
instance (a :<: g, TRSC g) => Convert a g where convertF t = inject(fmap reinject t)
-}


{-
class LabelWith a where
  type result a
  labelWith :: a -> [Int] -> result

instance LabelWith (Labelled a) where
    -}
