{-# LANGUAGE NoImplicitPrelude, PackageImports #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction, ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
module Control.Monad.Free where

import "monad-param" Control.Monad.Parameterized

import Control.Applicative
import qualified Control.Monad as Old
import qualified Control.Monad.Trans as Old
import Control.Monad.Operad
import Data.Foldable
import Data.Monoid
import Data.Traversable as T
import Prelude hiding (Monad(..))
import qualified Prelude

import TaskPoolSTM
-- This is the standard encoding of Free Monads, see e.g. http://comonad.com/reader/2008/monads-for-free

data Free f a = Impure (f (Free f a)) | Pure a

instance Functor f => Functor (Free f) where
    fmap f (Pure a)    = Pure   (f a)
    fmap f (Impure fa) = Impure (fmap (fmap f) fa)

instance (Functor f, Foldable f) => Foldable (Free f) where
    foldMap f (Pure a)    = f a
    foldMap f (Impure fa) = fold $ fmap (foldMap f) fa

instance Traversable f => Traversable (Free f) where
    traverse f (Pure a)   = Pure   <$> f a
    traverse f (Impure a) = Impure <$> traverse (traverse f) a

instance Functor f => Prelude.Monad (Free f) where
    return          = Pure
    Pure a    >>= f = f a
    Impure fa >>= f = Impure (fmap (>>= f) fa)

instance Return (Free f) where returnM = Pure
instance Functor f => Bind (Free f) (Free f) (Free f) where (>>=) = (Prelude.>>=)
instance Fail (Free f) where fail = error

evalFree :: (a -> b) -> (f(Free f a) -> b) -> Free f a -> b
evalFree p _ (Pure x)   = p x
evalFree _ i (Impure x) = i x

foldFree :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldFree pure _    (Pure   x) = pure x
foldFree pure imp  (Impure x) = imp (fmap (foldFree pure imp) x)

mapFree :: (Functor f, Functor g) => (forall a. f a -> g a) -> Free f a -> Free g a
mapFree eta (Pure a)   = Pure a
mapFree eta (Impure x) = Impure (fmap (mapFree eta) (eta x))


-- * Monad Transformer
--   (built upon Luke Palmer control-monad-free hackage package)
newtype FreeT f m a = FreeT { unFreeT :: m (Either a (f (FreeT f m a))) }

editEither l r = either (Left . l) (Right . r)
conj f = FreeT . f . unFreeT

instance (Functor f, Functor m) => Functor (FreeT f m) where
    fmap f = conj $ fmap (editEither f ((fmap.fmap) f))

instance (Functor f, Prelude.Monad m) => Prelude.Monad (FreeT f m) where
    return = FreeT . Prelude.return . Left
    m >>= f = FreeT $ unFreeT m Prelude.>>= \r ->
        case r of
             Left x   -> unFreeT $ f x
             Right xc -> Prelude.return . Right $ fmap (Prelude.>>= f) xc

instance (Functor f) => Old.MonadTrans (FreeT f) where
    lift = FreeT . Old.liftM Left

instance (Functor f, Return m) => Return (FreeT f m) where returnM = FreeT . returnM . Left

instance (Functor f, Monad m) => Bind (FreeT f m) (FreeT f m) (FreeT f m) where
    m >>= f = FreeT $ unFreeT m >>= \r ->
        case r of
             Left x   -> unFreeT $ f x
             Right xc -> returnM . Right $ fmap (>>= f) xc

instance (Functor f, Monad m) => Bind (Free f) (FreeT f m) (FreeT f m) where m >>= f = (wrap m `asTypeOf1` f undefined)  >>= f

liftFree :: (Functor f, Monad m) => (a -> Free f b) -> (a -> FreeT f m b)
liftFree f = wrap . f

foldFreeT :: (Traversable f, Monad m) => (a -> m b) -> (f b -> m b) -> FreeT f m a -> m b
foldFreeT p i m = unFreeT m >>= \r ->
              case r of
                Left   x -> p x
                Right fx -> join (liftM i (mapMP (foldFreeT p i) fx))


unwrap :: (Traversable f, Monad m) => FreeT f m a -> m(Free f a)
unwrap = foldFreeT (returnM . Pure) (returnM . Impure)

wrap :: (Functor f, Monad m) => Free f a -> FreeT f m a
wrap  = FreeT . foldFree (returnM . Left) (returnM . Right . fmap FreeT)

wrap' :: (Functor f, Monad m) => m(Free f a) -> FreeT f m a
wrap' = FreeT . join . liftM unFreeT . liftM wrap

-- To perform a side-effecting instantiation in parallel, we must
--  1. calculate all the shape of the current computation by unwraping to a pure Free monad,
--  2. look at it using the Operad induced monad (which separates the shape from the computations)
--  3. map the instantiation over that,
--  4. sequence in parallel,
--  5. and finally wrap back to a FreeT
--
-- Kind of convoluted, huh?
parBind :: (Traversable f) => Int -> FreeT f IO a -> (a -> FreeT f IO a) -> (FreeT f IO a)
parBind n m f = FreeT $ go (unwrap m >>= parBind' f >>= unFreeT . wrap . unE)
  where
   parBind' f val = do
         let (EM (MO op xx)) = fmap (liftM inE . unwrap . f) (inE val)
         xx' <-  parSequence n xx
         return (join (EM(MO op xx')))


mapMP   :: (Traversable t, Monad m) => (a -> m b) -> t a -> m (t b)
mapMP f = unwrapMonadP . traverse (WrapMonadP . f)
newtype WrappedMonadP m a = WrapMonadP { unwrapMonadP :: m a }

instance Monad m => Functor (WrappedMonadP m) where fmap f (WrapMonadP v) = WrapMonadP (liftM f v)

instance Monad m => Applicative (WrappedMonadP m) where
        pure = WrapMonadP . returnM
        WrapMonadP f <*> WrapMonadP v = WrapMonadP (f `ap` v)