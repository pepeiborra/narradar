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

module Narradar.Types.Labellings where

import Control.Parallel.Strategies
import Data.Foldable (Foldable(..))
import Text.PrettyPrint

import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term
import Narradar.Utils.Ppr

-- -----------------------
-- Named Term Signatures
-- -----------------------

type LS   = Labelled String
type LPS  = Labelled PS
type LPId = Identifier LPS
type LId  = Identifier LS

-- -----------
-- Labellings
-- -----------
type Label = [Int]
data Labelled a = Labelling {labelling::Label, unlabel::a} | Plain {unlabel::a} deriving (Eq)

instance Functor Labelled where
  fmap f (Plain a)      = Plain (f a)
  fmap f (Labelling l a) = Labelling l (f a)

instance Foldable Labelled where
  foldMap f (Plain a)      = f a
  foldMap f (Labelling _ a) = f a

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

instance Ppr a => Ppr (Labelled a) where
    ppr (Labelling l a) = ppr a <> text "_" <> (hcat $ map ppr l)
    ppr (Plain a)       = ppr a

instance NFData a => NFData (Labelled a) where
    rnf (Plain a) = rnf a
    rnf (Labelling ii a) = rnf ii `seq` rnf a

mapLabel :: (forall id. Label -> id -> Labelled id) -> (forall id. id -> Labelled id) -> Labelled id -> Labelled id
mapLabel f _  (Labelling ll i) = f ll i
mapLabel _ l0 (Plain i)        = l0 i

mapLabelT :: (Functor (f (Labelled id)), MapId f) => (forall id. Label -> id -> Labelled id) -> (forall id. id -> Labelled id) -> Term (f (Labelled id)) v -> Term (f (Labelled id)) v
mapLabelT f l0 = evalTerm return (Impure . mapId (mapLabel f l0))

setLabel :: (MapId f, Functor (f (Labelled id))) => Term (f (Labelled id)) v -> (forall id. id -> Labelled id) -> Term (f (Labelled id)) v
setLabel t l = mapLabelT (\_ -> l) l t
appendLabel t ll = mapLabelT (Labelling . (++ ll)) (Labelling ll) t


