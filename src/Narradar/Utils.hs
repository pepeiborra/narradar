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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, StandaloneDeriving #-}

module Narradar.Utils where

import           Control.DeepSeq
import           Control.Applicative
import           Control.Concurrent
import           Control.Exception                    (bracket)
import           Control.Monad                        (liftM, liftM2, ap, when, MonadPlus, msum)
import           Control.Monad.Identity               (Identity(..))
import           Control.Monad.ConstrainedNormal      (NF(..))
import           Control.Monad.Free                   (Free(..))
import           Control.Failure
import           Control.Monad.List                   (lift, ListT(..))
import           Control.Monad.State                  (State,StateT, MonadState(..), evalStateT)
import qualified Control.Monad.State.Strict           as Strict
import           Control.Monad.Writer                 (Writer, WriterT, MonadWriter(..))
import qualified Control.RMonad                       as R
--import qualified "monad-param" Control.Monad.Parameterized as P
import           Data.AlaCarte
import           Data.Array                           as A
import           Data.Array.Base                      (unsafeAt)
import qualified Data.Foldable                        as F
import           Data.Foldable                        (toList, foldMap, Foldable)
import qualified Data.Graph                           as G
import qualified Data.ByteString                      as BS
import qualified Data.ByteString.Lazy                 as LBS
import           Data.Functor.Constant
import           Data.Int
import           Data.List                            (group, sort, nubBy)
import qualified Data.List                            as List
import           Data.List.Split                      (chunk)
import           Data.Hashable
import           Data.Maybe
import           Data.Map                             (Map)
import           Data.Set                             (Set)
import           Data.String
import           Data.Term                            (Term, HasId, EqModulo(..))
import           Data.Monoid
import qualified Data.Map                             as Map
import qualified Data.Set                             as Set
import           Data.Sequence                        ((|>), singleton, viewl, viewr, ViewL(..), ViewR(..))
import qualified Data.Sequence                        as Seq
import           Data.Strict                          (Pair(..), (:!:))
import           Data.Suitable
import           Data.Traversable
import           Data.Typeable
import           Language.Prolog.Representation       as Prolog
import           Funsat.RPOCircuit.Symbols

import           System.IO
import           System.Directory
import           System.Process

import           Data.Term.Rules                      as Term
import           Narradar.Framework.Observe
import           Narradar.Framework.Ppr
--import           Narradar.Utils.Observe()
--import TRS.Utils hiding (size, parens, brackets, trace)

import           Prelude                              hiding (mapM)

import           Debug.Hoed.Observe                   hiding (O)
import qualified Debug.Hoed.Observe                   as Observe

-- ----------------
-- Debugging stuff
-- ----------------

#ifdef DEBUG
import qualified Debug.Trace
trace = Debug.Trace.trace
debug  msg = do {hPutStrLn stderr msg; hFlush stderr}
debug' msg = do {hPutStr stderr msg; hFlush stderr}
#else
{-# INLINE trace #-}
trace _ x = x
debug  _ = return ()
debug' _ = return ()
#endif

pprTrace = trace . render . pPrint
pprError = error . render . pPrint
echo = hPutStrLn stderr
echo' = hPutStr stderr


-- ----------
-- Type hints
-- ----------

isTerm1 :: Term (f id) v -> Term (f id) v
isTerm1 = id

data Proxy a
proxy = undefined

-- ---------------
-- Type wrappers
-- ---------------

data Comparable where
  Comparable :: (Typeable a, Eq a, NFData a, Observable a
                ) => a -> Comparable deriving (Typeable)
instance Eq Comparable where (==) = comparableEq
comparableEq = comparableEqO nilObserver
comparableEqO (Observe.O o oo) (Comparable a) (Comparable b) =
  let types = (o "a ::" (show $ typeOf a), o "b ::" (show $ typeOf b))
      res = o "cast" (cast (o "a" a)) == Just (o "b" b)
  in if res then res else deepseq types res
instance Observable Comparable where observer (Comparable a) = send "Comparable" (return Comparable << a)
instance NFData Comparable where rnf (Comparable a) = rnf a

-- --------------------------------
-- fmap / mapM / foldMap / toList n
-- --------------------------------
liftL :: MonadPlus m => [a] -> m a
liftL = msum . map return

fmap2 = fmap . fmap
fmap3 = fmap . fmap . fmap
fmap4 = fmap . fmap . fmap . fmap
fmap5 = fmap . fmap . fmap . fmap . fmap
(<$$>)   = fmap2
(<$$$>)  = fmap3
(<$$$$>) = fmap4

mapM2   = mapM . mapM
mapM3   = mapM . mapM . mapM
return2 = return . return

foldMap2 :: (Foldable t, Foldable t', Monoid m) => (a -> m) -> t(t' a) -> m
foldMap3 :: (Foldable t, Foldable t', Foldable t'',Monoid m) => (a -> m) -> t(t'(t'' a)) -> m
foldMap2 = foldMap . foldMap
foldMap3 = foldMap . foldMap2

toList3 ::  (Foldable t, Foldable t1, Foldable t2) => t (t1 (t2 b)) -> [b]
toList3 = (F.concatMap . F.concatMap) toList

-- ------------------------
-- Foldables / Traversables
-- ------------------------
unsafeZipWithGM :: (Traversable t1, Traversable t2, Monad m) => (a -> b -> m c) -> t1 a -> t2 b -> m(t2 c)
unsafeZipWithGM f t1 t2  = evalStateT (mapM zipG' t2) (toList t1)
       where zipG' y = do st <- get
                          case st of
                            []     -> error "unsafeZipWithGM: first is shorter than second"
                            (x:xx) -> do
                                    put xx
                                    lift (f x y)

unsafeZipWithG :: (Traversable t1, Traversable t2) => (a -> b -> c) -> t1 a -> t2 b -> t2 c
unsafeZipWithG f x y = runIdentity $ unsafeZipWithGM (\x y -> return (f x y)) x y

-- 'Safe' variants
-- ----------------
tailSafe []     = []
tailSafe (_:xx) = xx

safeAtM a i
 | A.bounds a `inRange` i = return (a ! i)
 | otherwise = failure "safeIx"

safeAt msg a i = fromMaybe (error ("safeAt:" ++ msg)) (safeAtM a i)

--safeAtL msg i _ | i < 0 
safeAtL msg [] _   = error ("safeAtL - index too large (" ++ msg ++ ")")
safeAtL msg (x:_) 0 = x
safeAtL msg (_:xx) i = safeAtL msg xx (pred i)

-- --------------
-- Miscellanea
-- --------------
none f = not . Prelude.any f

subsetOf :: Ord a => [a] -> Set a -> Bool
subsetOf s1 s2 = all (`Set.member` s2) s1

intersections [] = Set.empty
intersections xx = List.foldl1' Set.intersection xx

ignore :: Monad m => m a -> m ()
ignore m = m >> return ()

li :: MonadPlus m => [a] -> m a
li = msum . map return

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

fst3 :: (a,b,c) -> a
snd3 :: (a,b,c) -> b
fst3 (a,_,_) = a
snd3 (_,b,_) = b

fst4 :: (a,b,c,d) -> a
fst4 (a,_,_,_) = a

first3  :: (a -> a') -> (a,b,c) -> (a',b,c)
second3 :: (b -> b') -> (a,b,c) -> (a,b',c)
third3  :: (c -> c') -> (a,b,c) -> (a,b,c')
first3  f (a,b,c) = (f a, b, c)
second3 f (a,b,c) = (a, f b, c)
third3  f (a,b,c) = (a, b, f c)

firstM f (x,y) = f x >>= \x' -> return (x',y)
secondM f (x,y) = f y >>= \y' -> return (x,y')

showPpr = show . pPrint

snub :: Ord a => [a] -> [a]
snub = snubBy id
snubBy :: Ord a => (t -> a) -> [t] -> [t]
snubBy f = go Set.empty where
  go _   []     = []
  go acc (x:xx) = if fx `Set.member` acc then go acc xx else x : go (Set.insert fx acc) xx
    where fx = f x

(cmp `on` f) a b = cmp (f a) (f b)

--hashId :: Show a => a -> Int32
--hashId = HT.hashString . show

isRight Right{} = True; isRight _ = False
isLeft  Left{}  = True; isLeft  _ = False
fromLeft  (Left  l) = l
fromRight (Right a) = a
catLefts  xx = [ x | Left  x <- xx]
catRights xx = [ x | Right x <- xx]

eitherM :: (Monad m, Show err) => Either err a -> m a
eitherM = either (fail.show) return
{-
instance Show err => P.Bind (Either err) IO IO where
 m >>= f = eitherM m >>= f
-}
mapLeft :: (l -> l') -> Either l r -> Either l' r
mapLeft f (Left x)  = Left(f x)
mapLeft _ (Right r) = Right r

mapMif :: (Monad m, Traversable t) => (a -> Bool) -> (a -> m a) -> t a -> m (t a)
mapMif p f= mapM (\x -> if p x then f x else return x)

tag f xx = [ (f x, x) | x <- xx]

inhabiteds :: [[a]] -> [[a]]
inhabiteds = filter (not.null)

-- select = selectSafe ""

selectSafe :: String -> [Int] -> [a] -> [a]
selectSafe msg ii xx
  | len > 5   = map (safeIx (A.!) (A.listArray (0, len - 1) xx)) ii
  | otherwise = map (safeIx (!!) xx) ii
  where
    len = length xx
    safeIx :: (container a -> Int -> a) -> container a -> Int -> a
    safeIx (!!) xx i
        | i > len - 1 = error ("select(" ++ msg ++ "): index too large")
        | i < 0       = error ("select(" ++ msg ++ "): negative index")
        | otherwise = xx !! i

propSelect ii xx = map (xx!!) ii' == selectSafe "" ii' xx
  where _types = (xx::[Int], ii::[Int])
        ii'   = filter (< length xx) (map abs ii)


asTypeOf1 :: f a -> f b -> f a
asTypeOf1 x _ = x

asTypeOfArg1 :: f a -> g a -> f a
asTypeOfArg1 x _ = x

asTypeOfArg21 :: f a b -> f' a b' -> f a b
asTypeOfArg21 x _ = x

chunks = chunk

--withTempFile dir name m = bracket (openTempFile dir name) (removeFile . fst) (uncurry m)

withTempFile dir name m = do
  (fp, h) <- openTempFile dir name
  (delete, res)  <- m fp h
  when delete $ removeFile fp
  return res

-- Implementacion libre de:
--  "A new way to enumerate cycles in graph" - Hongbo Liu, Jiaxin Wang
--
-- TODO reimplementar liuwang con Data.Sequence
--cycles :: Graph gr => gr a b -> [[Node]]
cycles gr = filter (all ((==1) . length) . group) $ concatMap (map getNodes . liuwang) [singletonQ n | n <- G.vertices gr]
 where
  liuwang path = [ path | h `elem` safeAt "cycles" gr t] ++
                 concatMap liuwang [ snoc n path | n <- safeAt "cycles" gr t, n > h, n `notMemberQ` path]
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

-- ----------------------------------------------
-- Running external processes feeding bytestrings
-- ----------------------------------------------

readProcessWithExitCodeBS exec args input = do
        let nice = ""
        debug (unwords $ nice : exec : args)
        outMVar <- newEmptyMVar
        errMVar <- newEmptyMVar
        (hIn, hOut, hErr, hProc) <- runInteractiveProcess "time" (exec:args) Nothing Nothing
        (code, out, err) <- do
          _ <- forkIO (BS.hGetContents hOut >>= putMVar outMVar)
          _ <- forkIO (BS.hGetContents hErr >>= putMVar errMVar)
          when (not $ LBS.null input) $ LBS.hPut hIn input
          hClose hIn

          out <- takeMVar outMVar
          err <- takeMVar errMVar

          code <- waitForProcess hProc

          return (code, out, err)
        return (code, out, err)
  where
   ignore :: Monad m => a -> m ()
   ignore _ = return ()

-- --------------------------------------------
-- Hashable instances for Prolog representation
-- --------------------------------------------

instance Hashable id => Hashable (T id a) where
  hashWithSalt s (T id) = hashWithSalt s id

instance Hashable id => Hashable (K id a) where
  hashWithSalt s (K id) = hashWithSalt s id

instance Hashable PrologP_ where
  hashWithSalt s Is = 1 `hashWithSalt` s
  hashWithSalt s Eq = 2 `hashWithSalt` s
  hashWithSalt s Cut = 3 `hashWithSalt` s
  hashWithSalt s Ifte = 4 `hashWithSalt` s
  hashWithSalt s Not = 5 `hashWithSalt` s

instance Hashable PrologT_ where
  hashWithSalt s Zero = hashWithSalt s ( 1 :: Int)
  hashWithSalt s Succ = hashWithSalt s ( 2 :: Int)
  hashWithSalt s Tup  = hashWithSalt s ( 3 :: Int)
  hashWithSalt s Cons = hashWithSalt s ( 4 :: Int)
  hashWithSalt s Nil  = hashWithSalt s ( 5 :: Int)
  hashWithSalt s (String x) = hashWithSalt s x

instance (Hashable (f a), Hashable (g a)) => Hashable ((f:+:g) a) where
  hashWithSalt s (Inl f) = hashWithSalt s f
  hashWithSalt s (Inr g) = hashWithSalt s g

instance (Functor f, Hashable (f Int)) => Hashable (Expr f) where
  hashWithSalt s = foldExpr (hashWithSalt s)

-- -----------------------------------
-- Missing useful monadic instances
-- -----------------------------------

instance (Monoid w, MonadWriter w m) => MonadWriter w (ListT m) where
    tell = lift.tell

-- --------------------------------
-- RFunctor instance for Signature
-- --------------------------------
instance R.RFunctor Signature where
    fmap f sig@(Sig c d) =
        withConstraintsOf sig $ \SigConstraints -> withResConstraints $ \SigConstraints ->
              Sig (Map.mapKeys f c) (Map.mapKeys f d)

data instance Constraints Signature id = Ord id => SigConstraints
instance Ord id => Suitable Signature id where
   constraints = SigConstraints

-- -----------------------------
-- Missing (:!:) Monoid instance
-- -----------------------------

instance (Monoid a, Monoid b) => Monoid (Pair a b) where
  mempty = mempty :!: mempty
  mappend (a :!: b) (a' :!: b') = mappend a a' :!: mappend b b'

-- --------------------------------
-- Missing Typeable instances
-- --------------------------------
deriving instance Typeable NF
deriving instance Typeable Expr
deriving instance Typeable RuleF
deriving instance Typeable RPOSsymbol
deriving instance Typeable RPOsymbol
deriving instance Typeable LPOSsymbol
deriving instance Typeable LPOsymbol
deriving instance Typeable MPOsymbol
deriving instance Typeable Constant
deriving instance Typeable NFData
deriving instance Typeable Observable
deriving instance Typeable HasId
deriving instance Typeable EqModulo

-- -------------------------
-- Missing NFData instances
-- -------------------------
-- bogus instance for NF, as we cannot possibly force it
instance NFData (t a) => NFData (NF c t a) where rnf (FMap f t) = ()
deriving instance NFData a => NFData (EqModulo a)
-- ----------------------
-- Ord instance for Doc
-- ----------------------
instance Eq Doc where a == b = show a == show b
instance Ord Doc where compare a b = compare (show a) (show b)
