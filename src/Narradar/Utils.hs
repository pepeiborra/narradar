{-# LANGUAGE PackageImports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Utils (module Narradar.Utils, module TRS.Utils, HT.hashInt, HT.hashString) where

import Control.Applicative
import Control.Exception (bracket)
import Control.Monad (join, liftM, liftM2, replicateM, ap)
import Control.Monad.State (State,StateT)
import Data.Array.IArray
import Data.Foldable (toList, foldMap, Foldable)
import qualified Data.Graph  as G
import qualified Data.HashTable as HT
import Data.Int
import Data.List (group, sort,nub)
import Data.Monoid
import qualified Data.Set as Set
import Data.Sequence ((|>), singleton, viewl, viewr, ViewL(..), ViewR(..))
import qualified Data.Sequence as Seq
import Data.Traversable
import System.IO
import System.Directory
import Test.QuickCheck

import TRS.Utils hiding (size, parens, brackets, trace)

import Prelude hiding (mapM)

-- Type Constructor Composition
-- ----------------------------
newtype O f g x = O (f(g x))
instance (Functor f, Functor g) => Functor (O f g) where fmap f (O fgx) = O (fmap2 f fgx)

-- --------------
-- Various stuff
-- --------------

hashId :: Show a => a -> Int32
hashId = HT.hashString . show

isRight Right{} = True; isRight _ = False

mapLeft :: (l -> l') -> Either l r -> Either l' r
mapLeft f (Left x)  = Left(f x)
mapLeft f (Right r) = Right r

mapMif :: (Monad m, Traversable t) => (a -> Bool) -> (a -> m a) -> t a -> m (t a)
mapMif p f= mapM (\x -> if p x then f x else return x)

foldMap2 :: (Foldable t, Foldable t', Monoid m) => (a -> m) -> t(t' a) -> m
foldMap3 :: (Foldable t, Foldable t', Foldable t'',Monoid m) => (a -> m) -> t(t'(t'' a)) -> m
foldMap2 = foldMap . foldMap
foldMap3 = foldMap . foldMap2

inhabiteds :: [[a]] -> [[a]]
inhabiteds = filter (not.null)

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
--cycles :: Graph gr => gr a b -> [[Node]]
cycles gr = filter (all ((==1) . length) . group) $ concatMap (map getNodes . liuwang) [singletonQ n | n <- G.vertices gr]
 where
  liuwang path = [ path | h `elem` gr ! t] ++
                 concatMap liuwang [ snoc n path | n <- gr ! t, n > h, n `notMemberQ` path]
                     where h = headQ path
                           t = tailQ path
  getNodes = toList . fst

singletonQ n      = (Seq.singleton n, Set.singleton n)
memberQ n (_,set) = n `Set.member` set
notMemberQ n q    = not (memberQ n q)
headQ (viewl -> h:<_, _) = h
tailQ (viewr -> _:>t, _) = t
snoc n (seq, set) = (seq |> n, Set.insert n set)
{-
cycles_old :: Graph gr => gr a b -> [[Node]]
cycles_old gr = (snub  . map (sort.getNodes)) (concatMap liuwang [[(n,n)] | n <- nodes gr])
    where liuwang path = [ path ++ [closure] | let closure = (tpath, phead path), closure `elem` edges gr] ++
                        concatMap liuwang [path++[(tpath,n)] | n <- suc gr tpath, n /= hpath, (tpath,n) `notElem` path]
                            where tpath = ptail path
                                  hpath = phead path
          phead = fst . head
          ptail = snd . last
          getNodes = snub . map fst


propCycles gr = not (null$ nodes gr) ==> sort (sort <$> cycles (toG gr)) == sort (sort <$> cycles_old gr) where types = gr :: Gr () ()

toG gr = G.buildG bounds (edges gr)
         where bounds | null (nodes gr) = (0,0)
                      | otherwise = (minimum $ nodes gr, maximum $ nodes gr)

instance Arbitrary (Gr () ()) where
  arbitrary = do
      nodes <- arbitrary
      edges <- forM [0..nodes] $ \n -> do
                  n_edges <- arbitrary
                  edges   <- replicateM n_edges (choose (0,nodes))
                  return [ (n,e) | e <- edges ]
      return $ mkUGraph [0..nodes] (concat edges)
-}
-- -------------
-- Memoization
-- -------------

memoIO :: Eq a => (a -> Int32) -> (a -> IO b) -> IO (a -> IO b)
memoIO hash f = do
  ht <- HT.new (==) hash
  return (\x -> do
            prev <- HT.lookup ht x
            case prev of
              Just res -> return res
              Nothing  -> do
                        res <- f x
                        HT.insert ht x res
                        return res)

-- ------------------------------
-- Higher Rank boolean operators
-- ------------------------------
(.&.) = liftM2 (&&)
(.|.) = liftM2 (||)
infixr 3 .&.
infixr 3 .|.

(..&..) = (liftM2.liftM2) (&&)
(..|..) = (liftM2.liftM2) (||)
infixr 3 ..&..
infixr 3 ..|..

-- ---------------------------------------
-- Missing Applicative instance for StateT
-- ---------------------------------------
instance Monad m => Applicative (StateT s m) where pure = return; (<*>) = ap
instance Applicative (State s) where pure = return; (<*>) = ap
