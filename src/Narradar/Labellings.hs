{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE KindSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}

module Narradar.Labellings where

import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Bottom
import Narradar.Utils
import TRS

-- -----------------------
-- Named Term Signatures
-- -----------------------
--instance HashTerm (T PId) where hashF (T id tt) = 14 * sum tt * hashString (convert id)
--instance HashTerm (T PS)  where hashF (T id tt) = 14 * sum tt * hashString (convert id)
--instance HashTerm (T LPId) where hashF (T id tt) = 14 * sum tt * hashString (convert id)


type LPS  = Labelled PS
type LPId = Identifier LPS
type LId  = Identifier (Labelled String)

type BasicL     = Var :+: T (Labelled String) :+: Hole
type BBasicL    = Var :+: T (Labelled String) :+: Hole :+: Bottom
type BasicLId   = Var :+: T LId :+: Hole
type BBasicLId  = Var :+: T LId :+: Hole :+: Bottom
type BBasicLPId = Var :+: T LPId :+: Hole :+: Bottom
type BasicLPS   = Var :+: T LPS  :+: Hole
type BasicLPId  = Var :+: T LPId :+: Hole


instance HashConsed BasicL
instance HashConsed BBasicL
instance HashConsed BasicLId
instance HashConsed BBasicLPId
instance HashConsed BasicLPId
instance HashConsed BasicLPS
instance HashConsed BBasicLId

--instance DPMark BasicPId   PId
--instance DPMark BBasicPId  PId
--instance DPMark BBasicLPId LPId
--instance DPMark BBasicLId LId

-- -----------
-- Labellings
-- -----------
data Labelled a = Labelling {labelling::[Int], unlabel::a} | Plain {unlabel::a} deriving (Eq)

instance Ord a => Ord (Labelled a) where
    compare (Labelling i1 f1) (Labelling i2 f2) = compare (f1,i1) (f2,i2)
    compare (Plain f1) (Plain f2) = compare f1 f2
    compare Labelling{} Plain{} = GT
    compare Plain{} Labelling{} = LT

instance Show (Labelled String) where
    show (Labelling l a) = a ++ "_" ++ (concatMap show l)
    show (Plain a)       = a

instance Show a => Show (Labelled a) where
    show (Labelling l a) = show a ++ "_" ++ (concatMap show l)
    show (Plain a)       = show a

instance HashTerm (T LId) where
    hashF (T id tt)      = 15 * sum tt * hashId id
{-
instance Show id => DPSymbol (Labelled id) where
    markDPSymbol   (Labelling l id) = Labelling l (markDPSymbol id);   markDPSymbol   (Plain f) = Plain$ markDPSymbol f
    unmarkDPSymbol (Labelling l id) = Labelling l (unmarkDPSymbol id); unmarkDPSymbol (Plain f) = Plain$ unmarkDPSymbol f
    functionSymbol = Plain . functionSymbol
    dpSymbol       = Plain . dpSymbol
--    symbol (Plain f) = symbol f; symbol (Labelling _ f) = symbol f
-}

--labelWith (open -> Just (T (id::Identifier) tt)) labelling = term (Labelling labelling id) tt
--labelWith :: Term BBasicId -> [Int] -> Term BBasicLId -- (LabelledVersionOf f)
--labelWith :: forall f f' id. (ConvertT f f', T (Labelled id) :<: f', Var :<: f, HashConsed f, HashConsed f') => Term f -> [Int] -> Term f'
labelWith t= setLabel t

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


type family   LabelledVersionOf (f :: * -> *) :: * -> *
type instance LabelledVersionOf (T id)    = T (Labelled id)
type instance LabelledVersionOf Var       = Var
type instance LabelledVersionOf (a :+: b) = (LabelledVersionOf a :+: LabelledVersionOf b)
type instance LabelledVersionOf Bottom    = Bottom
type instance LabelledVersionOf Hole      = Hole

--instance (f' ~ LabelledVersionOf f, DPMark f id) => DPMark f' (Labelled id) where


