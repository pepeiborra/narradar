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

import "monad-param" Control.Monad.Parameterized
import "monad-param" Control.Monad.MonadPlus.Parameterized
import "control-monad-free" Control.Monad.Free hiding (Monad(..), join, mplus, liftM)
import Control.Monad.Free.Improve
import Control.Applicative
import qualified Control.Monad as Old
import qualified Control.Monad.Identity (Identity(..))
import qualified Control.Monad.Trans as Old
import Control.Monad.Operad
import Data.Foldable
import Data.Monoid
import Data.Traversable as T
import Prelude hiding (Monad(..), abs)
import qualified Prelude as P

import TaskPoolSTM

instance Return (Free f) where returnM = Pure
instance Functor f => Bind (Free f) (Free f) (Free f) where (>>=) = (P.>>=)
instance Fail (Free f) where fail = error

data AnnotatedF n f a = Annotated {note::n, dropNote::f a}
instance Functor f => Functor (AnnotatedF n f) where fmap f (Annotated n x) = Annotated n (fmap f x)
instance Foldable f => Foldable (AnnotatedF n f) where foldMap f (Annotated n x) = foldMap f x
instance Traversable f => Traversable (AnnotatedF n f) where traverse f (Annotated n x) = Annotated n <$> traverse f x
dropNotes = foldFree Pure (Impure . dropNote)
annotate :: Functor f => (a -> b) -> (Free f b -> n) -> Free f a -> Free (AnnotatedF n f) a
annotate p i = fmap fst . foldFree (\x -> Pure (x,p x)) (\x -> Impure (Annotated (i $ Impure $ fmap (dropNotes . fmap snd) x) x))

instance (Functor f) => MonadTrans (FreeT f) where
    lift = FreeT . liftM Left

instance (Functor f, Return m) => Return (FreeT f m) where returnM = FreeT . returnM . Left

instance (Functor f, Monad m) => Bind (FreeT f m) (FreeT f m) (FreeT f m) where (>>=) = (>>=)
instance (Functor f, Bind m m' m', Monad m') => Bind (FreeT f m) (FreeT f m') (FreeT f m') where
  m >>= f =
     FreeT (unFreeT m >>= \r ->
             case r of
               Left x   -> unFreeT (f x)
               Right xc -> returnM $ Right $ fmap (>>= f) xc
           )

instance (Functor f, Functor m, Old.Monad m) => Bind (Free f) (FreeT f m) (FreeT f m) where m >>= f = (trans m `asTypeOf1` f undefined)  Old.>>= f
instance (Functor f, Functor m, Old.Monad m) => Bind (FreeT f m) (Free f) (FreeT f m) where m >>= f = m Old.>>= \v -> (trans$ f v) `asTypeOf1` m

-- To perform a side-effecting instantiation in parallel, we must
--  1. calculate all the shape of the current computation by unwraping to a pure Free monad,
--  2. look at it using the Operad induced monad (which separates the shape from the computations)
--  3. map the instantiation over that,
--  4. sequence in parallel,
--  5. and finally wrap back to a FreeT
--
-- Kind of convoluted, huh?
parBind :: (Traversable f) => Int -> FreeT f IO a -> (a -> FreeT f IO b) -> (FreeT f IO b)
parBind n m f = FreeT $ go (untrans m >>= parBind' f >>= unFreeT . trans . unE)
  where
   parBind' f val = do
         let (EM (MO op xx)) = fmap (liftM inE . untrans . f) (inE val)
         xx' <-  parSequence n xx
         return (join (EM(MO op xx')))

-- Parallel binds

(>||>) :: forall a b c m f .
          (Bind m (FreeT f IO) (FreeT f IO), Traversable f) =>
          (a -> m b) -> (b -> FreeT f IO c) -> a -> FreeT f IO c
f >||> g = \x -> f x ||>> g

(||>>) :: forall a b c m f .
          (Bind m (FreeT f IO) (FreeT f IO), Traversable f) =>
          m a -> (a -> FreeT f IO b) -> FreeT f IO b
m ||>> g = parBind 4 (m >>= returnFreeT) g
  where returnFreeT :: a' -> FreeT f IO a'
        returnFreeT = returnM

instance Bind (C mu) (C mu) (C mu) where
  C p >>= k = C (\h -> p (\a -> case k a of C q -> q h))

instance Return (C mu) where
  returnM a = C (\h -> h a)

instance (P.Monad mu, MonadZero mu) => MonadZero (C mu) where mzeroM = rep mzeroM
instance (P.Monad mu, MPlus mu mu mu) => MPlus (C mu) (C mu) (C mu) where
    mplus p1 p2 = rep (mplus (improve p1) (improve p2))

asTypeOf1 :: f a -> f b -> f a
asTypeOf1 x y = x