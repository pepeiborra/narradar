{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}

module Narradar.TRS where

import Control.Applicative
import Data.Array.IArray
import Data.Graph (Graph)
import Data.Foldable
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Monoid
import Text.PrettyPrint

import TRS hiding (Ppr, ppr)
import qualified TRS
import Narradar.DPIdentifiers
import Narradar.Utils
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Syntax (Ident)

-- --------------------
-- TRSs in our setting
-- --------------------
data NarradarTRS id f where
    TRS       :: (Ord id, TRSC f, T id :<: f) => Set (Rule f)                -> Signature id -> NarradarTRS id f
    PrologTRS :: (Ord id, TRSC f, T id :<: f) => Set (Ident, Rule f)         -> Signature id -> NarradarTRS id f
    DPTRS     :: (Ord id, TRSC f, T id :<: f) => Array Int (Rule f) -> Graph -> Signature id -> NarradarTRS id f

type Edges = [(Int, Int)]

instance (Ord id, Ord (Term f), TRSC f, T id :<: f) => Ord (NarradarTRS id f) where
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BasicId) #-}
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BBasicId) #-}
    {-# off SPECIALIZE instance Ord(NarradarTRS LId BBasicLId) #-}
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _)   (DPTRS rr2 _ _)   = compare rr1 rr2

instance (Ord id, T id :<: f, TRSC f) => TRS (NarradarTRS id f) id f where
    {-# SPECIALIZE instance TRS(NarradarTRS Id BasicId) Id BasicId #-}
    {-# SPECIALIZE instance TRS(NarradarTRS Id BBasicId) Id BBasicId #-}
    {-# off SPECIALIZE instance TRS(NarradarTRS LId BBasicLId) LId BBasicLId #-}
    rules(TRS       rr _)   = toList rr
    rules(PrologTRS rr _)   = map snd (toList rr)
    rules(DPTRS     rr _ _) = elems rr
    tRS = narradarTRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS :: forall id f. (Ord id, TRSC f, T id :<: f) => [(Ident, Rule f)] -> NarradarTRS id f
prologTRS rr = prologTRS' (Set.fromList rr)

prologTRS' :: forall id f. (Ord id, TRSC f, T id :<: f) => Set(Ident, Rule f) -> NarradarTRS id f
prologTRS' rr = PrologTRS rr (getSignature (snd <$> toList rr))

{-# SPECIALIZE narradarTRS ::  [Rule BBasicId] -> NarradarTRS Id BBasicId #-}
narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)
dpTRS rules edges = DPTRS rules edges (getSignature $ elems rules)

rulesArray (DPTRS dps _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

instance Ord id => HasSignature (NarradarTRS id f) id where
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BasicId) Id #-}
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BBasicId) Id #-}
    {-# off SPECIALIZE instance HasSignature(NarradarTRS LId BBasicLId) LId #-}
    getSignature (TRS       _ sig) = sig
    getSignature (PrologTRS _ sig) = sig
    getSignature (DPTRS   _ _ sig) = sig

instance (T id :<: f, Ord id, TRSC f) => Monoid (NarradarTRS id f) where
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BasicId) #-}
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BBasicId) #-}
    {-# off SPECIALIZE instance Monoid(NarradarTRS LId BBasicLId) #-}
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature (snd <$> toList rr))
    mappend (DPTRS r1 e1 _) (DPTRS r2 e2 _) =
       let rr = elems r1 `mappend` elems r2 in TRS (Set.fromList rr) (getSignature rr)
    mappend emptytrs trs | null (rules emptytrs) = trs
    mappend trs emptytrs | null (rules emptytrs) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (T id :<: f, Ord id, TRSC f) =>  Size (NarradarTRS id f) where size = sizeTRS

instance TRS.Ppr f      => Ppr (NarradarTRS id f) where
    ppr trs@TRS{} = vcat $ map ppr $ rules trs
