{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Control.Monad.Operad where

import Control.Applicative
import Control.Monad.State  (runState, get, put)
import Control.Monad.Writer (runWriter, tell)
import Data.Foldable
import Data.Traversable
import Prelude as P hiding (mapM)

-- The Operad class
-- ----------------
class Operad a where
  identity :: a
  degree   :: a -> Int
  o        :: a -> [a] -> a


-- Shapes of computations (Monads as Operads)
-- ------------------------------------------

type Shape t = t ()

serialise :: Traversable t => t a -> (Shape t, [a])
serialise = runWriter . mapM (tell.atom) where atom x = [x]

deserialise :: Traversable t => Shape t -> [a] -> (t a, [a])
deserialise shape = runState (mapM f shape) where
    f () = do
      (x:xs) <- get
      put xs
      return x

newtype OperadWrapper m = O {unO :: Shape m}

instance (Traversable m, Monad m) => Operad (OperadWrapper m) where
  degree   = length . toList . unO
  identity = O (return ())
  O t `o` ts = let (r,[]) = deserialise t (map unO ts) in O(r >>= id)


-- Operads as Monads
-- ------------------

data MonadOperad op a = MO { shape :: op, value :: [a] } deriving (Eq, Show)
instance Functor     (MonadOperad o) where fmap     f (MO o xx) = MO o (map f xx)
instance Foldable    (MonadOperad o) where foldMap  f (MO o xx) = foldMap f xx
instance Traversable (MonadOperad o) where traverse f (MO o xx) = MO <$> pure o <*> traverse f xx

instance Operad o => Monad (MonadOperad o) where
    return x = MO identity [x]
    p >>= f  = join (fmap f p) where
        join (MO p xs) = MO (p `o` map shape xs) (P.concatMap value xs)


-- Isomorphism
-- -----------
asComp :: Traversable t => t x -> MonadOperad (Shape t) x
asComp t = uncurry MO (serialise t)

--asData :: Traversable t => MonadOperad (Shape t) x -> t x
asData (MO shape contents) = let (r,[]) = deserialise shape contents in r

--newtype MonadWrapper m = O


-- Efficient Monads
-- ----------------

newtype EfficientMonad m a = EM {unE'::MonadOperad (OperadWrapper m) a}
 deriving (Functor, Monad, Foldable, Traversable)


inE :: Traversable m => m a -> EfficientMonad m a
inE m = let (MO shape contents) = asComp m in EM(MO (O shape) contents)

unE :: Traversable m => EfficientMonad m a -> m a
unE (EM (MO shape contents)) = asData (MO (unO shape) contents)

--efficiently :: (Monad m, Traversable m) => m a -> m a
--efficiently = unE . inE

