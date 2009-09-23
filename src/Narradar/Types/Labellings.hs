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

import Control.Applicative
import Control.Parallel.Strategies
import Data.Foldable (Foldable(..), toList)
import Data.Traversable as T

import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term
import Narradar.Framework.Ppr

-- -----------------------
-- Named Term Signatures
-- -----------------------

type LS   = Labelled String
type LId  = Identifier LS

instance RemovePrologId a => RemovePrologId (Labelled a) where
  type WithoutPrologId (Labelled a) = Labelled (WithoutPrologId a)
  removePrologId = T.mapM removePrologId


-- -----------
-- Labellings
-- -----------
type Label = [Int]
data Labelled a = Labelling {labelling::Label, unlabel::a} | Plain {unlabel::a} deriving (Eq, Ord)

instance Functor Labelled where
  fmap f (Plain a)      = Plain (f a)
  fmap f (Labelling l a) = Labelling l (f a)

instance Foldable Labelled where
  foldMap f (Plain a)       = f a
  foldMap f (Labelling _ a) = f a

instance Traversable Labelled where
  traverse f (Plain a)       = Plain <$> f a
  traverse f (Labelling l a) = Labelling l <$> f a
{-
instance Ord a => Ord (Labelled a) where
    compare (Labelling i1 f1) (Labelling i2 f2) = compare (f1,i1) (f2,i2)
    compare (Plain f1) (Plain f2) = compare f1 f2
    compare Labelling{} Plain{} = GT
    compare Plain{} Labelling{} = LT
-}
instance Show (Labelled String) where
    show (Labelling l a) = a ++ "_" ++ (concatMap show l)
    show (Plain a)       = a

instance Show a => Show (Labelled a) where
    show (Labelling l a) = show a ++ "_" ++ (concatMap show l)
    show (Plain a)       = show a

instance Pretty a => Pretty (Labelled a) where
    pPrint (Labelling l a) = pPrint a <> text "_" <> (hcat $ map pPrint l)
    pPrint (Plain a)       = pPrint a

instance NFData a => NFData (Labelled a) where
    rnf (Plain a) = rnf a
    rnf (Labelling ii a) = rnf ii `seq` rnf a



class IsLabelled id where
    type WithoutLabel id :: *
    getLabel    :: id -> Maybe [Int]
    mapLabel :: (Maybe [Int] -> Maybe [Int]) -> id -> id

instance IsLabelled (Labelled a) where
    type WithoutLabel (Labelled a) = a
    getLabel Plain{} = Nothing; getLabel (Labelling ii _) = Just ii
    mapLabel f (Plain x)       = maybe (Plain x) (`Labelling` x) (f Nothing)
    mapLabel f (Labelling l x) = maybe (Plain x) (`Labelling` x) (f (Just l))

instance IsLabelled a => IsLabelled (PrologId a) where
   type WithoutLabel (PrologId a) = PrologId (WithoutLabel a)
   getLabel   = foldMap getLabel
   mapLabel f = fmap (mapLabel f)


instance IsLabelled a => IsLabelled (Identifier a) where
   type WithoutLabel (Identifier a) = Identifier (WithoutLabel a)
   getLabel   = foldMap getLabel
   mapLabel f = fmap (mapLabel f)


{-
mapLabel :: (forall id. Label -> id -> Labelled id) -> (forall id. id -> Labelled id) -> Labelled id -> Labelled id
mapLabel f _  (Labelling ll i) = f ll i
mapLabel _ l0 (Plain i)        = l0 i
-}
mapLabelT :: (MapId f, Functor (f id), IsLabelled id) => (Maybe [Int] -> Maybe [Int]) -> Term (f id) v -> Term (f id) v
mapLabelT f = evalTerm return (Impure . mapId (mapLabel f))

setLabel :: (MapId f, Functor (f id), IsLabelled id) => Term (f id) v -> Maybe [Int] -> Term (f id) v
setLabel t l = mapLabelT (\_ -> l) t

-- appendLabel t ll = mapLabelT (Labelling . (++ ll)) (Labelling ll) t


labelTerm :: (MapId t, Foldable (t id), Functor (t id), Functor (t (Labelled id))) =>
             (id -> Bool) -> Free (t id) v -> Free (t (Labelled id)) v
labelTerm pred = foldTerm return f where
  f t = Impure $ mapId (\id -> (if pred id then Labelling [1..length (toList t)] else Plain) $ id) t

{-
labelTerm1 :: (MapId t, Functor prologId, Foldable (t (prologId id)), Functor (t (prologId id)), Functor (t (prologId(Labelled id)))) =>
             (prologId id -> Bool) -> Free (t (prologId id)) v -> Free (t (prologId (Labelled id))) v
labelTerm1 pred = foldTerm return f where
  f t = Impure $ mapId (\id -> (if pred id then Labelling [1..length (toList t)] else Plain) <$> id) t
-}