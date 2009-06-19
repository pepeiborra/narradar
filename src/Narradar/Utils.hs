{-# LANGUAGE CPP #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleInstances, FlexibleContexts, TypeSynonymInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.Utils where

import Control.Applicative
import Control.Exception (bracket)
import Control.Monad (join, liftM, liftM2, replicateM, ap)
import Control.Monad.Identity(Identity(..))
import Control.Monad.List (lift, ListT)
import Control.Monad.State (State,StateT, MonadState(..), evalStateT)
import Control.Monad.Writer (Writer, WriterT, MonadWriter(..))
import qualified Control.RMonad as R
--import qualified "monad-param" Control.Monad.Parameterized as P
import Data.Array.IArray
import Data.Foldable (toList, foldMap, Foldable)
import qualified Data.Graph  as G
import qualified Data.HashTable as HT
import Data.Int
import Data.List (group, sort,nub)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Sequence ((|>), singleton, viewl, viewr, ViewL(..), ViewR(..))
import qualified Data.Sequence as Seq
import Data.Suitable
import Data.Traversable
import System.IO
import System.Directory
import Text.ParserCombinators.Parsec as P (GenParser, (<|>), pzero)
import Text.PrettyPrint

import Data.Term.Rules as Term
import Data.Term.Ppr as Term
--import TRS.Utils hiding (size, parens, brackets, trace)

import Prelude hiding (mapM)

#ifdef DEBUG
import qualified Debug.Trace
trace = Debug.Trace.trace
#else
{-# INLINE trace #-}
trace _ x = x
#endif

-- Type Constructor Composition
-- ----------------------------
newtype O f g x = O (f(g x))
instance (Functor f, Functor g) => Functor (O f g) where fmap f (O fgx) = O (fmap2 f fgx)

-- -------------
-- fmap / mapM
-- -------------
fmap2  = fmap . fmap
(<$$>) = fmap2

mapM2  = mapM . mapM

return2 = return . return

-- ------------------------
-- Foldables / Traversables
-- ------------------------
unsafeZipWithGM :: (Traversable t1, Traversable t2, Monad m) => (a -> b -> m c) -> t1 a -> t2 b -> m(t2 c)
unsafeZipWithGM f t1 t2  = evalStateT (mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          lift (f x y)

unsafeZipWithG :: (Traversable t1, Traversable t2) => (a -> b -> c) -> t1 a -> t2 b -> t2 c
unsafeZipWithG f x y = runIdentity $ unsafeZipWithGM (\x y -> return (f x y)) x y

--size = length . toList

foldMap2 :: (Foldable t, Foldable t', Monoid m) => (a -> m) -> t(t' a) -> m
foldMap3 :: (Foldable t, Foldable t', Foldable t'',Monoid m) => (a -> m) -> t(t'(t'' a)) -> m
foldMap2 = foldMap . foldMap
foldMap3 = foldMap . foldMap2

-- --------------
-- Various stuff
-- --------------
fst3 (a,b,c) = a
fst4 (a,b,c,d) = a

showPpr = show . ppr

snub :: Ord a => [a] -> [a]
snub = go Set.empty where
  go _   []     = []
  go acc (x:xx) = if x `Set.member` acc then go acc xx else x : go (Set.insert x acc) xx

(cmp `on` f) a b = cmp (f a) (f b)

hashId :: Show a => a -> Int32
hashId = HT.hashString . show

isRight Right{} = True; isRight _ = False

eitherM :: (Monad m, Show err) => Either err a -> m a
eitherM = either (fail.show) return
{-
instance Show err => P.Bind (Either err) IO IO where
 m >>= f = eitherM m >>= f
-}
mapLeft :: (l -> l') -> Either l r -> Either l' r
mapLeft f (Left x)  = Left(f x)
mapLeft f (Right r) = Right r

mapMif :: (Monad m, Traversable t) => (a -> Bool) -> (a -> m a) -> t a -> m (t a)
mapMif p f= mapM (\x -> if p x then f x else return x)

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

tailSafe []     = []
tailSafe (_:xx) = xx

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
{-# NOINLINE memoIO #-}
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
-- Missing Applicative instances
-- ---------------------------------------
instance Monad m => Applicative (StateT s m) where pure = return; (<*>) = ap
instance Applicative (State s) where pure = return; (<*>) = ap

instance (Monoid s, Monad m) => Applicative (WriterT s m) where pure = return; (<*>) = ap
--instance Applicative (Writer s) where pure = return; (<*>) = ap

-- -----------------------------------
-- Missing useful monadic instances
-- -----------------------------------

instance (Monoid w, MonadWriter w m) => MonadWriter w (ListT m) where tell = lift.tell

-- --------------------------------
-- RFunctor instance for Signature
-- --------------------------------
instance R.RFunctor Signature where
    fmap f sig@(Sig c d a) =
        withConstraintsOf sig $ \SigConstraints -> withResConstraints $ \SigConstraints ->
              Sig (Set.map f c) (Set.map f d) (Map.mapKeys f a)

instance Ord id => Suitable Signature id where
   data Constraints Signature id = Ord id => SigConstraints
   constraints _ = SigConstraints

-- --------------------------
-- RMonad instance for WriterT
-- --------------------------

instance (Monoid s) => Suitable (WriterT s m) a where
   data Constraints (WriterT s m) a = WriterTConstraints
   constraints _ = WriterTConstraints

instance (Monad m, Monoid s) => R.RFunctor (WriterT s m) where
   fmap = fmap

instance (Monoid s, Monad m) => R.RMonad (WriterT s m) where
   return = return
   (>>=) = (>>=)
   fail = fail

#ifndef TRANSFORMERS
instance (Monoid s) => Suitable (Writer s) a where
   data Constraints (Writer s) a = WriterConstraints
   constraints _ = WriterConstraints

instance (Monoid s) => R.RFunctor (Writer s) where
   fmap = fmap

instance (Monoid s) => R.RMonad (Writer s) where
   return = return
   (>>=) = (>>=)
   fail = fail
#endif
