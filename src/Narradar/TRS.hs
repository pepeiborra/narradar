{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}

module Narradar.TRS where

import Control.Applicative
import Data.Foldable
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Monoid

import TRS
import Narradar.DPIdentifiers
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Syntax (Ident)

-- --------------------
-- TRSs in our setting
-- --------------------
data NarradarTRS id f where
    TRS :: (Ord id, TRSC f, T id :<: f) => Set (Rule f) -> Signature id -> NarradarTRS id f
    PrologTRS :: (Ord id, TRSC f, T id :<: f) => Set (Ident, Rule f) -> Signature id -> NarradarTRS id f

instance (Ord id, Ord (Term f), TRSC f, T id :<: f) => Ord (NarradarTRS id f) where
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BasicId) #-}
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BBasicId) #-}
    {-# off SPECIALIZE instance Ord(NarradarTRS LId BBasicLId) #-}
    compare TRS{} PrologTRS{} = LT
    compare PrologTRS{} TRS{} = GT
    compare (TRS rr1 _) (TRS rr2 _)             = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2

instance (Ord id, T id :<: f, TRSC f) => TRS (NarradarTRS id f) id f where
    {-# SPECIALIZE instance TRS(NarradarTRS Id BasicId) Id BasicId #-}
    {-# SPECIALIZE instance TRS(NarradarTRS Id BBasicId) Id BBasicId #-}
    {-# off SPECIALIZE instance TRS(NarradarTRS LId BBasicLId) LId BBasicLId #-}
    rules(TRS rr _)       = toList rr
    rules(PrologTRS rr _) = map snd (toList rr)
    tRS = narradarTRS

{-# SPECIALIZE narradarTRS ::  [Rule BBasicId] -> NarradarTRS Id BBasicId #-}
narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)

instance Ord id => HasSignature (NarradarTRS id f) id where
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BasicId) Id #-}
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BBasicId) Id #-}
    {-# off SPECIALIZE instance HasSignature(NarradarTRS LId BBasicLId) LId #-}
    getSignature (TRS _ sig)       = sig
    getSignature (PrologTRS _ sig) = sig


instance (T id :<: f, Ord id, TRSC f) => Monoid (NarradarTRS id f) where
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BasicId) #-}
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BBasicId) #-}
    {-# off SPECIALIZE instance Monoid(NarradarTRS LId BBasicLId) #-}
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature (snd <$> toList rr))
    mappend emptytrs trs | null (rules emptytrs) = trs
    mappend trs emptytrs | null (rules emptytrs) = trs

    mappend x y = error "error: are you sure you want to mappend different kinds of TRSs?" `const` x `const` y

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS :: forall id f. (Ord id, TRSC f, T id :<: f) => [(Ident, Rule f)] -> NarradarTRS id f
prologTRS rr = prologTRS' (Set.fromList rr)

prologTRS' :: forall id f. (Ord id, TRSC f, T id :<: f) => Set(Ident, Rule f) -> NarradarTRS id f
prologTRS' rr = PrologTRS rr (getSignature (snd <$> toList rr))
