{-# LANGUAGE PackageImports #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Utils where

import Control.Applicative
import Control.Exception (bracket)
import Control.Monad (join, liftM)
import qualified "monad-param" Control.Monad.Parameterized as MonadP
import Data.Graph.Inductive (nodes, edges, suc, Graph, Node(..))
import Data.List (group, sort)
import Data.Traversable
import qualified Data.Set as Set
import System.IO
import System.Directory

import Prelude hiding (mapM)

fmap2, (<$$>) :: (Functor f, Functor g) => (a -> b) -> f(g a) -> f (g b)
fmap2 = fmap.fmap
(<$$>) = fmap2

concatMapM :: (Monad t, Monad m, Traversable t) => (a -> m (t b)) -> t a -> m (t b)
concatMapM f = liftM join . mapM f
concatMapMP :: (MonadP.Monad t, MonadP.Monad m, Traversable t) => (a -> m (t b)) -> t a -> m (t b)
concatMapMP f = MonadP.liftM MonadP.join . mapMP f

mapMP   :: (Traversable t, MonadP.Monad m) => (a -> m b) -> t a -> m (t b)
mapMP f = unwrapMonadP . traverse (WrapMonadP . f)
newtype WrappedMonadP m a = WrapMonadP { unwrapMonadP :: m a }

instance MonadP.Monad m => Functor (WrappedMonadP m) where fmap f (WrapMonadP v) = WrapMonadP (MonadP.liftM f v)

instance MonadP.Monad m => Applicative (WrappedMonadP m) where
        pure = WrapMonadP . MonadP.returnM
        WrapMonadP f <*> WrapMonadP v = WrapMonadP (f `MonadP.ap` v)

mapMif :: (Monad m, Traversable t) => (a -> Bool) -> (a -> m a) -> t a -> m (t a)
mapMif p f= mapM (\x -> if p x then f x else return x)


inhabiteds :: [[a]] -> [[a]]
inhabiteds = filter (not.null)

snub :: Ord a => [a] -> [a]
snub  = Set.toList . Set.fromList

on :: (t1 -> t1 -> t2) -> (t -> t1) -> t -> t -> t2
on cmp f x y = cmp (f x) (f y)

select :: (Ord t, Enum t, Num t) => [a] -> [t] -> [a]
select xx ii = go 0 xx (sort ii)
    where go _ [] _ = []
          go _ _ [] = []
          go n (x:xx) (i:ii) | n == i = x : go (succ n) xx ii
                             | otherwise = go (succ n) xx (i:ii)

propSelect xx ii = map (xx!!) ii' == select xx ii'
  where types = (xx::[Int], ii::[Int])
        ii'   = filter (< length xx) (map abs ii)


asTypeOf1 :: f a -> f b -> f a
asTypeOf1 x _ = x

chunks n _ | n < 1 = error "chunks: zero or negative chunk size"
chunks _ []   = []
chunks n list = xx : chunks n rest  where (xx, rest) = (take n list, drop n list)

withTempFile dir name m = bracket (openTempFile dir name) (removeFile . fst) (uncurry m)

-- Implementacion libre de:
--  "A new way to enumerate cycles in graph" - Hongbo Liu, Jiaxin Wang
--
-- TODO reimplementar liuwang con Data.Sequence
cycles :: Graph gr => gr a b -> [[Node]]
cycles gr = (snub  . map (sort . getNodes)) (concatMap liuwang [[(n,n)] | n <- nodes gr])
    where liuwang path = [ path ++ [closure] | let closure = (tpath, phead path), closure `elem` edges gr] ++
                        concatMap liuwang [path++[(tpath,n)] | n <- suc gr tpath, n /= hpath, (tpath,n) `notElem` path]
                                    where tpath = ptail path
                                          hpath = phead path
          phead = fst . head
          ptail = snd . last
          getNodes = snub . map fst
