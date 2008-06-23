module Utils where

import Control.Monad (join, liftM)
import Data.Graph.Inductive (nodes, edges, suc, Graph, Node(..))
import Data.List (group, sort)
import Data.Traversable

import Prelude hiding (mapM)

fmap2 :: (Functor f, Functor g) => (a -> b) -> f(g a) -> f (g b)
fmap2 = fmap.fmap

concatMapM :: (Monad t, Monad m, Traversable t) => (a -> m (t a)) -> t a -> m (t a)
concatMapM f = liftM join . mapM f

mapMif :: (Monad m, Traversable t) => (a -> Bool) -> (a -> m a) -> t a -> m (t a)
mapMif p f= mapM (\x -> if p x then f x else return x)


inhabiteds :: [[a]] -> [[a]]
inhabiteds = filter (not.null)

snub :: Ord a => [a] -> [a]
snub  = map head . group . sort

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
