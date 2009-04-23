{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE KindSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}

module Narradar.Labellings where

import Control.Parallel.Strategies
import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Utils
import TRS.Bottom
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
type Label = [Int]
data Labelled a = Labelling {labelling::Label, unlabel::a} | Plain {unlabel::a} deriving (Eq)

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

instance NFData a => NFData (Labelled a) where
    rnf (Plain a) = rnf a
    rnf (Labelling ii a) = rnf ii `seq` rnf a

mapLabel :: (forall id. Label -> id -> Labelled id) -> (forall id. id -> Labelled id) -> Labelled id -> Labelled id
mapLabel f _  (Labelling ll i) = f ll i
mapLabel f l0 (Plain i)        = l0 i

mapLabelT :: MapLabelT f => (forall id. Label -> id -> Labelled id) -> (forall id. id -> Labelled id) -> Term f -> Term f
mapLabelT f l0 = mapTerm (mapLabelTF f l0)

class MapLabelT' f f => MapLabelT f; instance MapLabelT' f f => MapLabelT f
class (f :<: g) => MapLabelT' f g where mapLabelTF :: (forall id. Label -> id -> Labelled id) -> (forall id. id -> Labelled id) -> f (Term g) -> Term g; mapLabelTF _ _ = inject

instance (T (Labelled id) :<: g) => MapLabelT' (T (Labelled id)) g where mapLabelTF f l0 (T id tt) = inject (T (mapLabel f l0 id) tt)
instance (MapLabelT' f g, MapLabelT' f' g, (f:+:f') :<: g) => MapLabelT' (f :+: f') g where
    mapLabelTF f l0 (Inr x) = mapLabelTF f l0 x; mapLabelTF f l0 (Inl x) = mapLabelTF f l0 x
--instance (T id :<: g) => MapLabelT' (T id) g
instance (Hole :<: g) => MapLabelT' Hole   g
instance (Var  :<: g) => MapLabelT' Var    g

setLabel ::  (MapLabelT f, HashConsed f) => Term f -> (forall id. id -> Labelled id) -> Term f
setLabel t l = mapLabelT (\_ -> l) l t
appendLabel t ll = mapLabelT (Labelling . (++ ll)) (Labelling ll) t

type family   LabelledVersionOf (f :: * -> *) :: * -> *
type instance LabelledVersionOf (T id)    = T (Labelled id)
type instance LabelledVersionOf Var       = Var
type instance LabelledVersionOf (a :+: b) = (LabelledVersionOf a :+: LabelledVersionOf b)
type instance LabelledVersionOf Bottom    = Bottom
type instance LabelledVersionOf Hole      = Hole

--instance (f' ~ LabelledVersionOf f, DPMark f id) => DPMark f' (Labelled id) where


