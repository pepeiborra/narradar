{-# LANGUAGE PackageImports #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE Rank2Types, NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

module Control.Monad.Free.Narradar
      (module Control.Monad.Free,
       module Control.Monad.Free.Improve,
       module Control.Monad.Free.Narradar) where

import "control-monad-free" Control.Monad.Free hiding (Monad(..), join, mplus, liftM)
import Control.Monad.Free.Improve
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Traversable as T
import Prelude hiding (abs)
import qualified Prelude as P

data AnnotatedF n f a = Annotated {note::n, dropNote::f a}
instance Functor f => Functor (AnnotatedF n f) where fmap f (Annotated n x) = Annotated n (fmap f x)
instance Foldable f => Foldable (AnnotatedF n f) where foldMap f (Annotated _ x) = foldMap f x
instance Traversable f => Traversable (AnnotatedF n f) where traverse f (Annotated n x) = Annotated n <$> traverse f x
dropNotes = foldFree Pure (Impure . dropNote)
annotate :: Functor f => (a -> b) -> (Free f b -> n) -> Free f a -> Free (AnnotatedF n f) a
annotate p i = fmap fst . foldFree (\x -> Pure (x,p x))
               (\x -> Impure (Annotated (i $ Impure $ fmap (dropNotes . fmap snd) x) x))
