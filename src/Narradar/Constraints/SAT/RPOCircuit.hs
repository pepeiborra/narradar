{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-| Extension of Funsat.Circuit to generate RPO constraints as boolean circuits

-}
module Narradar.Constraints.SAT.RPOCircuit
   (Circuit(..)
   ,ECircuit(..)
   ,NatCircuit(..)
   ,OneCircuit(..)
   ,RPOCircuit(..)
   ,RPOExtCircuit(..)
   ,FreshCircuit(..)
   ,CastCircuit(..), CastRPOCircuit(..)
   ,HasPrecedence(..), precedence
   ,HasFiltering(..), listAF, inAF
   ,HasStatus(..), useMul, lexPerm
   ,Shared(..), FrozenShared(..), runShared
   ,EvalM, Eval, EvalF(..), runEval, runEvalM, evalB, evalN
   ,Graph(..), shareGraph, shareGraph'
   ,Tree(..), printTree
   ,CircuitProblem(..), ECircuitProblem(..), RPOCircuitProblem(..)
   ,CNF(..), CNFBS(..), asDimacs
   ,removeComplex, removeComplex'
   ,toCNF, toCNFBS, toCNFRPO
   ,projectCircuitSolution, projectECircuitSolution, projectRPOCircuitSolution
   ) where

{-
    This file is heavily based on parts of funsat.

    funsat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    funsat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with funsat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}

import Control.Applicative
import Control.Arrow (first, second)
import Control.Exception as CE (assert)
import Control.Monad.Reader
import Control.Monad.State.Strict hiding ((>=>), forM_)
import Data.BiTrie( (:<->:) )
import Data.ByteString.Lazy.Char8 (ByteString)
import Data.Foldable (Foldable, foldMap)
import Data.List( nub, foldl', sortBy, (\\))
import Data.Map( Map )
import Data.Maybe( fromJust )
import Data.NarradarTrie (HasTrie, (:->:) )
import Data.Monoid
import Data.Set( Set )
import Data.Traversable (Traversable, traverse, fmapDefault, foldMapDefault)
import Prelude hiding( not, and, or, (>) )

import Funsat.ECircuit ( Circuit(..)
                       , ECircuit(..)
                       , NatCircuit(..)
                       , FreshCircuit(..)
                       , CastCircuit(..)
                       , CircuitHash, falseHash, trueHash
                       , Eval, EvalF(..), BEnv, runEval, fromBinary
                       , CircuitProblem(..), ECircuitProblem(..)
--                       , toCNF, toCNFBS
                       , projectCircuitSolution, projectECircuitSolution
                       , CNFBS(..), asDimacs)
import Funsat.Types( CNF(..), Lit(..), Var(..), var, lit, Solution(..), litSign, litAssignment )

import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types hiding (Var,V,var,fresh)
import Narradar.Utils ( selectSafe, safeAtL )

import System.Directory (getTemporaryDirectory)
import System.FilePath
import System.IO

import qualified Data.BiTrie as BiTrie
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import qualified Data.NarradarTrie as Trie
import qualified Funsat.Circuit  as Circuit
import qualified Funsat.ECircuit as ECircuit
import qualified Prelude as Prelude

class Circuit repr => OneCircuit repr where
    -- | @one bb = length (filter id bb) == 1@
    one  :: (Ord var, HasTrie var, Show var) => [repr var] -> repr var
    one  = oneDefault
{-
oneDefault :: (Ord v, Show v, ECircuit repr, FreshCircuit repr) => [repr v] -> repr v
oneDefault [] = false
oneDefault vv = let
          ones     = replicate (length vv) fresh
          zeros    = replicate (length vv) fresh
          encoding = foldr and true
                  [ (one_i  `iff` ite b_i zero_i1 one_i1) `and`
                    ( zero_i `iff` (not b_i `and` zero_i1))
                   | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                      zip5 vv ones zeros (tail ones ++ [false]) (tail zeros ++ [true])
                  ]
          in head ones `and` encoding
      where
       zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee)
           = (a,b,c,d,e) : zip5 aa bb cc dd ee
       zip5 _ _ _ _ _ = []
-}
oneDefault :: (Ord v, HasTrie v, Show v, Circuit repr) => [repr v] -> repr v
oneDefault [] = false
oneDefault (v:vv) = (v `and` none vv) `or` (not v `and` oneDefault vv)
  where
   none = foldr and true . map not

class NatCircuit repr => RPOCircuit repr id | repr -> id where
    termGt, termEq :: (HasPrecedence v id, HasFiltering v id, HasStatus v id
                      ,Ord v, Show v, HasTrie v) =>
                      TermN id -> TermN id -> repr v

class RPOCircuit repr id => RPOExtCircuit repr id where
    exGt, exEq :: (HasPrecedence v id, HasFiltering v id, HasStatus v id
                  ,Ord v, HasTrie v, Show v) =>
               id -> id -> [TermN id] -> [TermN id] -> repr v

class HasPrecedence v a | a -> v where precedence_vv :: a -> [v]
class HasFiltering  v a | a -> v where listAF_v      :: a -> v
                                       inAF_v        :: Int -> a -> v
class HasStatus v id | id -> v   where useMul_v      :: id -> v
                                       lexPerm_vv    :: id -> Maybe [[v]]

precedence :: (NatCircuit repr, HasPrecedence v id, Ord v, HasTrie v,  HasTrie v, Show v) => id -> repr v
precedence = nat . precedence_vv
listAF :: (Circuit repr, HasFiltering v id, Ord v, HasTrie v,  Show v) => id -> repr v
listAF     = input . listAF_v
inAF   :: (Circuit repr, HasFiltering v id, Ord v, HasTrie v,  Show v) => Int -> id -> repr v
inAF i     = input . inAF_v i
useMul :: (Circuit repr, HasStatus v id, Ord v, HasTrie v,  Show v) => id -> repr v
useMul     = input . useMul_v
lexPerm :: (Circuit repr, HasStatus v id, Ord v, HasTrie v,  Show v) => id -> Maybe [[repr v]]
lexPerm    = (fmap.fmap.fmap) input . lexPerm_vv

data NoId
instance HasPrecedence v NoId
instance HasStatus v NoId
instance HasFiltering v NoId

class CastRPOCircuit c cOut id where
  castRPOCircuit :: (HasPrecedence v id, HasFiltering v id, HasStatus v id, Ord v, HasTrie v, Show v) => c id v -> cOut v

newtype WrapCircuit c id v = WrapCircuit {wrappedCircuit :: c v}

instance CastCircuit Circuit.Tree c => CastRPOCircuit (WrapCircuit Circuit.Tree) c NoId where
    castRPOCircuit = castCircuit . wrappedCircuit
instance CastCircuit ECircuit.Tree c => CastRPOCircuit (WrapCircuit ECircuit.Tree) c NoId where
    castRPOCircuit = castCircuit . wrappedCircuit

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShared'.
newtype Shared id var = Shared { unShared :: State (CMaps id var) CCode }

-- | A shared circuit that has already been constructed.
data FrozenShared id var = FrozenShared !CCode !(CMaps id var) deriving Eq

frozenShared code maps = FrozenShared code maps


instance (HasTrie id, Show id, HasTrie var, Show var) => Show (FrozenShared id var) where
  showsPrec p (FrozenShared c maps) = ("FrozenShared " ++) . showsPrec p c . showsPrec p maps{hashCount=[]}


-- | Reify a sharing circuit.
runShared :: (HasTrie id, Ord id, HasTrie var) => Shared id var -> FrozenShared id var
runShared = runShared' emptyCMaps

runShared' :: (HasTrie id, Ord id, HasTrie var) => CMaps id var -> Shared id var -> FrozenShared id var
runShared' maps = uncurry frozenShared . (`runState` emptyCMaps) . unShared

getChildren :: (Ord v, HasTrie v) => CCode -> CircuitHash :<->: v -> v
getChildren code codeMap =
    case BiTrie.lookup (circuitHash code) codeMap of
      Nothing -> findError
      Just c  -> c
  where findError = error $ "getChildren: unknown code: " ++ show code

instance (HasTrie id, Ord id, ECircuit c, NatCircuit c, FreshCircuit c) => CastCircuit (Shared id) c where
    castCircuit = castCircuit . runShared

instance (ECircuit c, NatCircuit c, FreshCircuit c) => CastCircuit (FrozenShared id) c where
    castCircuit (FrozenShared code maps) = go code
      where
        go (CTrue{})     = true
        go (CFalse{})    = false
        go (CFresh c)    = internalVar c
        go c@(CVar{})    = input $ getChildren c (varMap maps)
        go c@(CAnd{})    = uncurry and    . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = uncurry or     . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = not            . go  $ getChildren c (notMap maps)
        go c@(CXor{})    = uncurry xor    . go2 $ getChildren c (xorMap maps)
        go c@(COnlyif{}) = uncurry onlyif . go2 $ getChildren c (onlyifMap maps)
        go c@(CIff{})    = uncurry iff    . go2 $ getChildren c (iffMap maps)
        go c@(CIte{})    = uncurry3 ite   . go3 $ getChildren c (iteMap maps)
        go c@CEq{}       = uncurry eq     . go2 $ getChildren c (eqMap maps)
        go c@CLt{}       = uncurry lt     . go2 $ getChildren c (ltMap maps)
        go c@CNat{}      = nat $ getChildren c (natMap maps)
        go c@COne{}      = oneDefault $ map go $ getChildren c (oneMap maps)

        go2 = (go `onTup`)
        go3 (x, y, z) = (go x, go y, go z)
        uncurry3 f (x, y, z) = f x y z
        onTup f (x,y) = (f x, f y)

instance (HasTrie id, Ord id, ECircuit c, NatCircuit c, FreshCircuit c) => CastRPOCircuit Shared c id where
    castRPOCircuit = castCircuit

instance (ECircuit c, NatCircuit c, FreshCircuit c) => CastRPOCircuit FrozenShared c id where
    castRPOCircuit = castCircuit

data CCode    = CTrue   { circuitHash :: !CircuitHash }
              | CFalse  { circuitHash :: !CircuitHash }
              | CVar    { circuitHash :: !CircuitHash }
              | CAnd    { circuitHash :: !CircuitHash }
              | COr     { circuitHash :: !CircuitHash }
              | CNot    { circuitHash :: !CircuitHash }
              | CXor    { circuitHash :: !CircuitHash }
              | COnlyif { circuitHash :: !CircuitHash }
              | CIff    { circuitHash :: !CircuitHash }
              | CIte    { circuitHash :: !CircuitHash }
              | CNat    { circuitHash :: !CircuitHash }
              | CEq     { circuitHash :: !CircuitHash }
              | CLt     { circuitHash :: !CircuitHash }
              | COne    { circuitHash :: !CircuitHash }
              | CFresh  { circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show, Read)

instance HasTrie CCode where
  newtype CCode :->: x = CCodeTrie (CircuitHash :->: (CCode, x))
  empty = CCodeTrie Trie.empty
  lookup cc (CCodeTrie t) = fmap snd $ Trie.lookup (circuitHash cc) t
  insert cc v (CCodeTrie t) = CCodeTrie (Trie.insert (circuitHash cc) (cc,v) t)
  toList (CCodeTrie t) = map snd $ Trie.toList t

-- | Maps used to implement the common-subexpression sharing implementation of
-- the `Circuit' class.  See `Shared'.
data CMaps id var = CMaps
    { hashCount :: ![CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.  Should not
    -- include 0 or 1.

    , varMap    :: !(CircuitHash :<->: var)
     -- ^ Mapping of generated integer IDs to variables.
    , freshSet  :: !(Set CircuitHash)
    , andMap    :: !(CircuitHash :<->: (CCode, CCode))
    , orMap     :: !(CircuitHash :<->: (CCode, CCode))
    , notMap    :: !(CircuitHash :<->: CCode)
    , xorMap    :: !(CircuitHash :<->: (CCode, CCode))
    , onlyifMap :: !(CircuitHash :<->: (CCode, CCode))
    , iffMap    :: !(CircuitHash :<->: (CCode, CCode))
    , iteMap    :: !(CircuitHash :<->: (CCode, CCode, CCode))
    , natMap    :: !(CircuitHash :<->: [var])
    , eqMap     :: !(CircuitHash :<->: (CCode, CCode))
    , ltMap     :: !(CircuitHash :<->: (CCode, CCode))
    , oneMap    :: !(CircuitHash :<->: [CCode])
    , termGtMap :: !((TermN id, TermN id) :->: CCode)
    , termEqMap :: !((TermN id, TermN id) :->: CCode)
    }

deriving instance (HasTrie id, Show id, HasTrie var, Show var) => Show (CMaps id var)
deriving instance (Eq id, HasTrie id, Eq var, HasTrie var) => Eq (CMaps id var)


-- | A `CMaps' with an initial `hashCount' of 2.
emptyCMaps :: (HasTrie id, Ord id, HasTrie var) => CMaps id var
emptyCMaps = CMaps
    { hashCount = [2 ..]
    , varMap    = mempty
    , freshSet  = Set.empty
    , andMap    = mempty
    , orMap     = mempty
    , notMap    = mempty
    , xorMap    = mempty
    , onlyifMap = mempty
    , iffMap    = mempty
    , iteMap    = mempty
    , natMap    = mempty
    , eqMap     = mempty
    , ltMap     = mempty
    , oneMap    = mempty
    , termGtMap = mempty
    , termEqMap = mempty
    }

-- prj: "projects relevant map out of state"
-- upd: "stores new map back in state"
{-# INLINE recordC #-}
recordC :: (Ord a, HasTrie a) =>
           (CircuitHash -> b)
        -> (CMaps id var -> Int :<->: a)            -- ^ prj
        -> (CMaps id var -> Int :<->: a -> CMaps id var) -- ^ upd
        -> a
        -> State (CMaps id var) b
recordC _ _ _ x | x `seq` False = undefined
recordC cons prj upd x = do
  s <- get
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (BiTrie.insert c x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ BiTrie.lookupR x (prj s)


instance Circuit (Shared id) where
    false = Shared falseS
    true  = Shared trueS
    input v = Shared $ recordC CVar varMap (\s e -> s{ varMap = e }) v
    and = liftShared2 and_ where
        and_ c@CFalse{} _ = return c
        and_ _ c@CFalse{} = return c
        and_ CTrue{} c  = return c
        and_ c CTrue{}  = return c
        and_ hl hr = recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)

    or = liftShared2 or_ where
        or_ c@CTrue{} _ = return c
        or_ _ c@CTrue{} = return c
        or_ CFalse{} c  = return c
        or_ c CFalse{}  = return c
        or_ hl hr = recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)
    not = liftShared notS


instance FreshCircuit (Shared id) where
    internalVar c = Shared $ do
        modify $ \s -> s{freshSet = Set.insert c (freshSet s)}
        return (CFresh c)
    fresh k  = Shared $ do
        c:cs <- gets hashCount
        modify $ \s -> s{freshSet = Set.insert c (freshSet s), hashCount=cs}
        unShared . k . Shared . return . CFresh $ c

instance ECircuit (Shared id) where
    xor = liftShared2 xor_ where
        xor_ CTrue{} c = notS c
        xor_ c CTrue{} = notS c
        xor_ CFalse{} c = return c
        xor_ c CFalse{} = return c
        xor_ hl hr = recordC CXor xorMap (\s e' -> s{ xorMap = e' }) (hl, hr)
    iff = liftShared2 iffS
    onlyif = liftShared2 onlyif_ where
        onlyif_ CFalse{} _ = trueS
        onlyif_ c CFalse{} = notS c
        onlyif_ CTrue{}  c = return c
        onlyif_ _ CTrue{}  = trueS
        onlyif_ hl hr
           | hl == hr  = trueS
           | otherwise = recordC COnlyif onlyifMap (\s e' -> s{ onlyifMap = e' }) (hl, hr)
    ite x t e = Shared $ do
        hx <- unShared x
        ht <- unShared t ; he <- unShared e
        ite_ hx ht he
      where
        ite_ CTrue{} ht _  = return ht
        ite_ CFalse{} _ he = return he
        ite_ hx ht he = recordC CIte iteMap (\s e' -> s{ iteMap = e' }) (hx, ht, he)

instance OneCircuit (Shared id) where
    one ss = Shared $ do
               xx <- sequence $ map unShared ss
               if null xx then falseS else recordC COne oneMap (\s e' -> s{oneMap = e'}) xx

instance NatCircuit (Shared id) where
    eq xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 if x == y then trueS else recordC CEq eqMap (\s e -> s {eqMap = e}) (x,y)

    lt xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 if x == y then falseS else recordC CLt ltMap (\s e -> s {ltMap = e}) (x,y)
    nat = Shared . recordC CNat natMap (\s e -> s{ natMap = e })

instance (Ord id, HasTrie id, RPOExtCircuit (Shared id) id) => RPOCircuit (Shared id) id where
 termGt s t = Shared $ do
      env <- get
      case Trie.lookup (s,t) (termGtMap env) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termGt_ s t
           modify $ \env -> env{termGtMap = Trie.insert (s,t) me (termGtMap env)}
           return me
   where (termGt_, _) = mkTermFunctions
 termEq s t = Shared $ do
      env <- get
      case (Trie.lookup (s,t) (termEqMap env)) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termEq_ s t
           modify $ \env -> env{termEqMap = Trie.insert (s,t) me (termEqMap env)}
           return me
   where (_, termEq_) = mkTermFunctions

{-# INLINE mkTermFunctions #-}
mkTermFunctions :: (Ord id, HasTrie id, RPOExtCircuit (Shared id) id
                   ,HasStatus var id, HasPrecedence var id, HasFiltering var id
                   ,Ord var, HasTrie var, Show var) =>
                   (TermN id -> TermN id -> Shared id var, TermN id -> TermN id -> Shared id var)
mkTermFunctions = (termGt_, termEq_) where
 termGt_ s t
    | s == t = false

    | Just id_t <- rootSymbol t, tt_t <- directSubterms t
    , Just id_s <- rootSymbol s, tt_s <- directSubterms s
    = cond1 id_s id_t tt_s tt_t `or` cond2 id_s tt_s

    | Just id_s <- rootSymbol s, tt_s <- directSubterms s
    = cond2 id_s tt_s

    | otherwise = false
   where
    cond1 id_s id_t tt_s tt_t
      = all (\(t_j, j) -> inAF j id_t --> (s > t_j))
            (zip tt_t [1..])
        `and`
        (listAF id_t --> and (listAF id_s)
                             (or (precedence id_s `gt` precedence id_t)
                                 (and (precedence id_s `eq` precedence id_t)
                                      (exGt id_s id_t tt_s tt_t))))

    cond2 id_s tt_s
      = any (\(s_i,i) -> inAF i id_s `and`
                         ((s_i > t) `or` (listAF id_s `and` (s_i ~~ t))))
            (zip tt_s [1..])
 termEq_ (Pure s) (Pure t) = if s == t then true else false
 termEq_ s t
   | s == t  = true
   | isVar s = not(listAF id_t) `and`
               all (\(t_j,j) -> inAF j id_t --> s ~~ t_j)
                   (zip tt [1..])
   | isVar t = not(listAF id_s) `and`
               all (\(s_i,i) -> inAF i id_s --> s_i ~~ t)
                   (zip ss [1..])

   | id_s == id_t
   = ite (listAF id_s)
         (exEq id_s id_t ss tt)
         (all (\(s_i,i) -> inAF i id_s --> s_i ~~ t) (zip ss [1..]))

   | otherwise
   = ite (listAF id_s)
         (ite (listAF id_t)
              ((precedence id_s `eq` precedence id_t) `and` exEq id_s id_t ss tt)
              (all (\(t_j,j) -> inAF j id_t --> t_j ~~ s) (zip tt [1..])))
         (all (\(s_i,i) -> inAF i id_s --> s_i ~~ t) (zip ss [1..]))

   where
     ss = directSubterms s
     tt = directSubterms t
     ~(Just id_s) = rootSymbol s
     ~(Just id_t) = rootSymbol t

 all f = foldr and true . map f
 any f = foldr or false . map f

 infixr 8 >
 infixr 8 ~~
 infixr 7 -->

 s > t   = termGt s t
 s ~~ t  = termEq s t
 a --> b = onlyif a b



falseS, trueS :: State (CMaps id var) CCode
falseS = return $ CFalse falseHash
trueS  = return $ CTrue trueHash

notS CTrue{}  = falseS
notS CFalse{} = trueS
notS (CNot i) = do {s <- get; return $ fromJust $ BiTrie.lookup i (notMap s) }
notS h        = recordC CNot notMap (\s e' -> s{ notMap = e' }) h

iffS CTrue{} c  = return c
iffS c CTrue{}  = return c
iffS CFalse{} c = notS c
iffS c CFalse{} = notS c
iffS hl hr
 | hl == hr  = trueS
 | otherwise = recordC CIff iffMap (\s e' -> s{ iffMap = e' }) (hl, hr)

{-# INLINE liftShared #-}
liftShared f a = Shared $ do {h <- unShared a; f h}
{-# INLINE liftShared2 #-}
liftShared2 f a b = Shared $ do
  va <- unShared a
  vb <- unShared b
  f va vb


-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.
data Tree id v = TTrue
               | TFalse
               | TLeaf v
               | TNot (Tree id v)
               | TAnd (Tree id v) (Tree id v)
               | TOr  (Tree id v) (Tree id v)
               | TXor (Tree id v) (Tree id v)
               | TIff (Tree id v) (Tree id v)
               | TOnlyIf (Tree id v) (Tree id v)
               | TIte (Tree id v) (Tree id v) (Tree id v)
               | TEq  (Tree id v) (Tree id v)
               | TLt  (Tree id v) (Tree id v)
               | TOne [Tree id v]
               | TNat [v]
               | TTermEq (TermN id) (TermN id)
               | TTermGt (TermN id) (TermN id)
                 deriving (Show, Eq, Ord)

foldTree :: (t -> v -> t) -> t -> Tree id v -> t
foldTree _ i TTrue        = i
foldTree _ i TFalse       = i
foldTree f i (TLeaf v)    = f i v
foldTree f i (TAnd t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TOr t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TNot t)     = foldTree f i t
foldTree f i (TXor t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TIff t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TOnlyIf t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TIte x t e) = foldTree f (foldTree f (foldTree f i x) t) e
foldTree f i (TEq t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TLt t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TOne tt)    = foldl (foldTree f)  i tt
foldTree f i (TNat xx)    = foldr (flip f) i xx
foldTree f i TTermEq{}    = i
foldTree f i TTermGt{}    = i

printTree :: (Pretty id, Pretty v) => Int -> Tree id v -> Doc
printTree _ TTrue        = text "true"
printTree _ TFalse       = text "false"
printTree p (TLeaf v)    = pPrint v
printTree p (TNot t)     = pP p 9 $ text "!" <> pt 9 t
printTree p (TAnd t1 t2) = pP p 5 $ pt 5 t1 <+> text "&" <+> pt 5 t2
printTree p (TOr  t1 t2) = pP p 5 $ pt 5 t1 <+> text "||" <+> pt 5 t2
printTree p (TXor t1 t2) = pP p 5 $ pt 5 t1 <+> text "xor" <+> pt 5 t2
printTree p (TIff t1 t2) = pP p 3 $ pt 3 t1 <+> text "<->" <+> pt 3 t2
printTree p (TOnlyIf t1 t2) = pP p 3 $ pt 3 t1 <+> text "-->" <+> pt 3 t2
printTree p (TIte c t e) = pP p 2 $ text "IFTE" <+> (pt 1 c $$ pt 1 t $$ pt 1 e)
printTree p (TEq (TNat n1) (TNat n2)) = pP p 7 (pPrint n1 <+> text "==" <+> pPrint n2)
printTree p (TLt (TNat n1) (TNat n2)) = pP p 7 (pPrint n1 <+> text "<" <+> pPrint n2)
printTree p (TOne vv) = pP p 1 $ text "ONE" <+> (hsep $ punctuate comma $ map (pt 1) vv)

pt p = printTree p
pP prec myPrec doc = if myPrec < prec then doc else parens doc

instance (ECircuit c, NatCircuit c, OneCircuit c) =>
  CastCircuit (Tree id) c
   where
    castCircuit (TTrue :: Tree id var) = true
    castCircuit TFalse       = false
    castCircuit (TLeaf l)    = input l
    castCircuit (TAnd t1 t2) = and (castCircuit t1) (castCircuit t2)
    castCircuit (TOr t1 t2)  = or (castCircuit t1) (castCircuit t2)
    castCircuit (TXor t1 t2) = xor (castCircuit t1) (castCircuit t2)
    castCircuit (TNot t)     = not (castCircuit t)
    castCircuit (TIff t1 t2) = iff (castCircuit t1) (castCircuit t2)
    castCircuit (TOnlyIf t1 t2) = onlyif (castCircuit t1) (castCircuit t2)
    castCircuit (TIte x t e) = ite (castCircuit x) (castCircuit t) (castCircuit e)
    castCircuit (TEq t1 t2)  = eq (castCircuit t1) (castCircuit t2)
    castCircuit (TLt t1 t2)  = lt (castCircuit t1) (castCircuit t2)
    castCircuit (TNat vv)    = nat vv
    castCircuit (TOne tt)    = one (map castCircuit tt)
    castCircuit c@(TTermEq t u) = error "cannot cast RPO constraints"
    castCircuit c@(TTermGt t u) = error "cannot cast RPO constraints"

instance (ECircuit c, NatCircuit c, OneCircuit c, RPOCircuit c id) =>
  CastRPOCircuit Tree c id
   where
    castRPOCircuit (TTrue :: Tree id var) = true
    castRPOCircuit TFalse       = false
    castRPOCircuit (TLeaf l)    = input l
    castRPOCircuit (TAnd t1 t2) = and (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TOr t1 t2)  = or (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TXor t1 t2) = xor (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TNot t)     = not (castRPOCircuit t)
    castRPOCircuit (TIff t1 t2) = iff (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TOnlyIf t1 t2) = onlyif (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TIte x t e) = ite (castRPOCircuit x) (castRPOCircuit t) (castRPOCircuit e)
    castRPOCircuit (TEq t1 t2)  = eq (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TLt t1 t2)  = lt (castRPOCircuit t1) (castRPOCircuit t2)
    castRPOCircuit (TNat vv)    = nat vv
    castRPOCircuit (TOne tt)    = one (map castRPOCircuit tt)
    castRPOCircuit c@(TTermEq t u) = termEq t u
    castRPOCircuit c@(TTermGt t u) = termGt t u

instance Functor (Tree id) where fmap = fmapDefault
instance Foldable (Tree id) where foldMap = foldMapDefault
instance Traversable (Tree id) where
  traverse f TTrue  = pure TTrue
  traverse f TFalse = pure TFalse
  traverse f (TLeaf v) = TLeaf <$> f v
  traverse f (TNot t) = TNot <$> traverse f t
  traverse f (TAnd t1 t2) = TAnd <$> traverse f t1 <*> traverse f t2
  traverse f (TOr  t1 t2) = TOr  <$> traverse f t1 <*> traverse f t2
  traverse f (TXor t1 t2) = TXor <$> traverse f t1 <*> traverse f t2
  traverse f (TIff t1 t2) = TIff <$> traverse f t1 <*> traverse f t2
  traverse f (TOnlyIf t1 t2) = TOnlyIf <$> traverse f t1 <*> traverse f t2
  traverse f (TEq t1 t2)  = TEq <$> traverse f t1 <*> traverse f t2
  traverse f (TLt t1 t2)  = TLt <$> traverse f t1 <*> traverse f t2
  traverse f (TIte t1 t2 t3) = TIte <$> traverse f t1 <*> traverse f t2 <*> traverse f t3
  traverse f (TOne tt)    = TOne <$> (traverse.traverse) f tt
  traverse f (TNat vv)    = TNat <$> traverse f vv
  traverse f (TTermGt t u)= TTermGt <$> pure t <*> pure u
  traverse f (TTermEq t u)= TTermEq <$> pure t <*> pure u

instance Circuit (Tree id) where
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot

instance ECircuit (Tree id) where
    xor   = TXor
    iff   = TIff
    onlyif = TOnlyIf
    ite   = TIte

instance NatCircuit (Tree id) where
    eq    = TEq
    lt    = TLt
    nat   = TNat

instance OneCircuit (Tree id) where
    one   = TOne

instance RPOCircuit (Tree id) id where
    termGt = TTermGt
    termEq = TTermEq

--    ------------------
-- ** Circuit evaluator
--    ------------------
newtype Flip t a b = Flip {unFlip::t b a}
type EvalM = Flip EvalF

fromLeft :: Either l r -> l
fromLeft (Left l) = l
fromRight :: Either l r -> r
fromRight (Right r) = r

runEvalM :: Map e Bool -> EvalM e a -> a
runEvalM env = flip unEval env . unFlip

instance Functor (EvalM v) where fmap f (Flip (Eval m)) = Flip $ Eval $ \env -> f(m env)
instance Monad (EvalM v) where
  return x = Flip $ Eval $ \_ -> x
  m >>= f  = Flip $ Eval $ \env -> runEvalM env $ f $ runEvalM env m

instance MonadReader (BEnv v) (EvalM v) where
  ask       = Flip $ Eval $ \env -> env
  local f m = Flip $ Eval $ \env -> runEvalM (f env) m

instance OneCircuit Eval where
    one tt    = Eval (\env -> Right $ case filter id $  map (fromRight . (`unEval` env)) tt of
                                        (_:[]) -> True
                                        _ -> False)

instance (Ord id, Pretty id) => RPOCircuit Eval id
  where
   termGt t u = unFlip (Right `liftM` (>)  evalRPO t u)
   termEq t u = unFlip (Right `liftM` (~~) evalRPO t u)

data RPOEval v a = RPO {(>), (>~), (~~) :: a -> a -> Flip EvalF v Bool}

evalB :: Eval v -> EvalM v Bool
evalN :: Eval v -> EvalM v Integer
evalB c = liftM (fromRight :: Either Integer Bool -> Bool) (eval c)
evalN c = liftM (fromLeft  :: Either Integer Bool -> Integer) (eval c)
eval  c = do {env <- ask; return (runEval env c)}

evalRPO :: forall id v.
           (Eq id, Ord id, Pretty id, HasPrecedence v id, HasStatus v id, HasFiltering v id
           ,Ord v, HasTrie v, Show v
           ) => RPOEval v (TermN id)
evalRPO = RPO{..} where

  infixr 4 >
  infixr 4 >~
  infixr 4 ~~

  s >~ t = s > t <|> s ~~ t

  s ~~ t
   | s == t = return True

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t = do
     af_s <- compFiltering s
     af_t <- compFiltering t
     case (af_s,af_t) of
      (Left i, _) -> safeAtL "RPOCircuit:673" tt_s (pred i) ~~ t
      (_, Left j) -> s ~~ safeAtL "RPOCircuit:674" tt_t (pred j)
      (_,_) -> evalB (precedence id_s `eq` precedence id_t) <&> exeq s t

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering s
     case af_s of
      Left i-> safeAtL "RPOCircuit:680" tt_s (pred i) ~~ t
      _     -> return False

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t = do
     af_t <- compFiltering t
     case af_t of
      Left j -> s ~~ safeAtL "RPOCircuit:686" tt_t (pred j)
      _      -> return False

   | otherwise = return False

  s > t

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering s
     af_t <- compFiltering t
     case (af_s, af_t) of
      (Left i, _) -> safeAtL "RPOCircuit:698" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "RPOCircuit:699" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> (evalB (precedence id_s `gt` precedence id_t)
                                                                   <|>
                                                              (evalB (precedence id_s `eq` precedence id_t) <&>
                                                               exgt s t)))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering s
     case af_s of
       Left  i  -> safeAtL "RPOCircuit:709" tt_s (pred i) > t
       Right ii -> anyM (>~ t) (sel 5 ii tt_s)

   | otherwise = return False

  exgt, exeq :: TermN id -> TermN id -> Flip EvalF v Bool
  exgt s t
   | Just id_t <- rootSymbol t, tt <- directSubterms t
   , Just id_s <- rootSymbol s, ss <- directSubterms s = do
        af_s <- AF.singleton' id_s `liftM` compFiltering s
        af_t <- AF.singleton' id_t `liftM` compFiltering t
        let ss' = directSubterms (AF.apply af_s s)
            tt' = directSubterms (AF.apply af_t t)
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True,  True)  -> mulD ss' tt'
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexsD (removeFiltered ps) (removeFiltered pt) ss tt

  exeq s t
   | Just id_t <- rootSymbol t, tt <- directSubterms t
   , Just id_s <- rootSymbol s, ss <- directSubterms s = do
        af_s <- AF.singleton' id_s `liftM` compFiltering s
        af_t <- AF.singleton' id_t `liftM` compFiltering t
        let ss' = directSubterms (AF.apply af_s s)
            tt' = directSubterms (AF.apply af_t t)
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True,  True)  -> muleqD ss' tt'
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexseqD (removeFiltered ps) (removeFiltered pt) ss tt

--  evalPerm :: HasStatus id v => id -> Flip Eval v (Maybe [Int])
  evalPerm id = do
    bits <- (T.mapM . mapM . mapM) evalB (lexPerm id)
    let perm = (fmap.fmap)
                 (\perm_i -> head ([i | (i,True) <- zip [1..] perm_i] ++ [-1]))
                 bits
    return perm

  compFiltering t | Just id <- rootSymbol t = do
    isList    <- evalB (listAF id)
    filtering <- mapM (\i -> evalB (inAF i id)) [1..length (directSubterms t)]
    let positions = [ i | (i, True) <- zip [1..] filtering ]
    return $ if isList then Right positions
             else CE.assert (length positions == 1) $ Left (head positions)

--  removeFiltered :: Functor f => f [Int] -> f [Int]
  removeFiltered = fmap ( filter (/= (-1)))

  lexD []     _      = return False
  lexD _      []     = return True
  lexD (f:ff) (g:gg) = (f > g) <|> (f ~~ g <&> lexD ff gg)

  lexeqD []     []     = return True
  lexeqD _      []     = return False
  lexeqD []     _      = return False
  lexeqD (f:ff) (g:gg) = (f ~~ g <&> lexeqD ff gg)

  lexsD f_perm g_perm ff gg = lexD (maybe ff (permute ff) f_perm)
                                   (maybe gg (permute gg) g_perm)
  lexseqD f_perm g_perm ff gg = lexeqD (maybe ff (permute ff) f_perm)
                                       (maybe gg (permute gg) g_perm)

  mulD m1 m2 = forall m2' $ \y-> exists m1' (> y)
   where
        m1' = m1 \\ m2
        m2' = m2 \\ m1

  muleqD m1 m2
    | length m1 /= length m2 = return False
    | otherwise = forall m2' $ \y-> exists m1' (~~ y)
     where
        m1' = m1 \\ m2
        m2' = m2 \\ m1

  infixr 3 <&>
  infixr 2 <|>

  (<|>) = liftM2 (||)
  (<&>) = liftM2 (&&)

  forall = flip allM
  exists = flip anyM
  allM  f xx = Prelude.and `liftM` mapM f xx
  anyM  f xx = Prelude.or  `liftM` mapM f xx

  sel n ii = selectSafe ("Narradar.Constraints.SAT.RPOCircuit.Eval - " ++ show n) (map pred ii)
  permute ff ii = map fst $ dropWhile ( (<0) . snd) $ sortBy (compare `on` snd) (zip ff ii)
  on cmp f x y = f x `cmp` f y

  sel6 = sel 6
  sel7 = sel 7
  sel8 = sel 8
  sel9 = sel 9

{-
  infixr 4 >
  infixr 4 >~
  infixr 4 ~~

  s >~ t = s > t <|> s ~~ t

  s ~~ t
   | s == t = return True

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t

   = evalB (precedence id_s `eq` precedence id_t) <&> exeq id_s id_t tt_s tt_t

   | otherwise = return False

  s > t
   | s == t = return False
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = anyM (>~ t) tt_s <|>
     (allM (s >) tt_t
      <&> evalB (precedence id_s `gt` precedence id_t)
           <|>
          (evalB (precedence id_s `eq` precedence id_t)
           <&> exgt id_s id_t tt_s tt_t))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   = anyM (>~ t) tt_s

   | otherwise = return False

  exgt id_s id_t ss tt = do
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True, True) -> mulD ss tt
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexsD (removeFiltered ps) (removeFiltered pt) ss tt

  exeq id_s id_t ss tt = do
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True, True) -> muleqD ss tt
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexseqD (removeFiltered ps) (removeFiltered pt) ss tt

--  evalPerm :: HasStatus id v => id -> Flip Eval v (Maybe [Int])
  evalPerm id = do
    bits <- (T.mapM . mapM . mapM) evalB (lexPerm id)
    let perm = (fmap.fmap)
                 (\perm_i -> head ([i | (i,True) <- zip [1..] perm_i] ++ [-1]))
                 bits
    return perm

--  removeFiltered :: Functor f => f [Int] -> f [Int]
  removeFiltered = fmap ( filter (/= (-1)))

  lexD []     _      = return False
  lexD _      []     = return True
  lexD (f:ff) (g:gg) =    (f > g)
                                <|> (f ~~ g <&> lexD ff gg)

  lexeqD []     []     = return True
  lexeqD _      []     = return False
  lexeqD []     _      = return False
  lexeqD (f:ff) (g:gg) = (f ~~ g <&> lexeqD ff gg)


  lexsD f_perm g_perm ff gg = lexD (maybe ff (permute ff) f_perm)
                                   (maybe gg (permute gg) g_perm)
  lexseqD f_perm g_perm ff gg = lexeqD (maybe ff (permute ff) f_perm)
                                       (maybe gg (permute gg) g_perm)

  mulD m1 m2 = muleqD m1 m2
                  <&>
               (exists m1' $ \x -> exists m2' $ \y -> x > y)
   where
        m1' = m1 \\ m2
        m2' = m2 \\ m1

  muleqD m1 m2 = forall m2' $ \y-> exists m1' $ \x -> x ~~ y
     where
        m1' = m1 \\ m2
        m2' = m2 \\ m1

  infixr 3 <&>
  infixr 2 <|>

  (<|>) = liftM2 (||)
  (<&>) = liftM2 (&&)

  forall = flip allM
  exists = flip anyM
  allM  f xx = Prelude.and `liftM` mapM f xx
  anyM  f xx = Prelude.or  `liftM` mapM f xx

  sel = selectSafe "Narradar.Constraints.RPO"
  permute ff ii = map fst $ dropWhile ( (<0) . snd) $ sortBy (compare `on` snd) (zip ff ii)
  on cmp f x y = f x `cmp` f y
-}


-- ** Graph circuit

-- | A circuit type that constructs a `G.Graph' representation.  This is useful
-- for visualising circuits, for example using the @graphviz@ package.
newtype Graph v = Graph
    { unGraph :: State Graph.Node (Graph.Node,
                                    [Graph.LNode (NodeType v)],
                                    [Graph.LEdge EdgeType]) }

-- | Node type labels for graphs.
data NodeType v = NInput v
                | NTrue
                | NFalse
                | NAnd
                | NOr
                | NNot
                | NXor
                | NIff
                | NOnlyIf
                | NIte
                | NNat [v]
                | NEq
                | NLt
                | NOne
                | NTermGt String String
                | NTermEq String String
                  deriving (Eq, Ord, Show, Read)

data EdgeType = ETest -- ^ the edge is the condition for an `ite' element
              | EThen -- ^ the edge is the /then/ branch for an `ite' element
              | EElse -- ^ the edge is the /else/ branch for an `ite' element
              | EVoid -- ^ no special annotation
              | ELeft
              | ERight
                 deriving (Eq, Ord, Show, Read)

runGraph :: (G.DynGraph gr) => Graph v -> gr (NodeType v) EdgeType
runGraph graphBuilder =
    let (_, nodes, edges) = evalState (unGraph graphBuilder) 1
    in Graph.mkGraph nodes edges

instance Circuit Graph where
    input v = Graph $ do
        n <- newNode
        return $ (n, [(n, NInput v)], [])

    true = Graph $ do
        n <- newNode
        return $ (n, [(n, NTrue)], [])

    false = Graph $ do
        n <- newNode
        return $ (n, [(n, NFalse)], [])

    not gs = Graph $ do
        (node, nodes, edges) <- unGraph gs
        n <- newNode
        return (n, (n, NNot) : nodes, (node, n, EVoid) : edges)

    and    = binaryNode NAnd EVoid EVoid
    or     = binaryNode NOr EVoid EVoid

instance ECircuit Graph where
    xor    = binaryNode NXor EVoid EVoid
    iff    = binaryNode NIff EVoid EVoid
    onlyif = binaryNode NOnlyIf ELeft ERight
    ite x t e = Graph $ do
        (xNode, xNodes, xEdges) <- unGraph x
        (tNode, tNodes, tEdges) <- unGraph t
        (eNode, eNodes, eEdges) <- unGraph e
        n <- newNode
        return (n, (n, NIte) : xNodes ++ tNodes ++ eNodes
               , (xNode, n, ETest) : (tNode, n, EThen) : (eNode, n, EElse)
                 : xEdges ++ tEdges ++ eEdges)

instance NatCircuit Graph where
    eq     = binaryNode NEq EVoid EVoid
    lt     = binaryNode NLt ELeft ERight
    nat xx = Graph $ do {n <- newNode; return (n, [(n, NNat xx)],[])}

instance OneCircuit Graph where
    one tt = Graph$ do
      (tips, nodes, edges) <- unzip3 `liftM` mapM unGraph tt
      me <- newNode
      let nodes' = (me, NOne) : concat nodes
          edges' = [(n, me, EVoid) | n <- tips ] ++ concat edges
      return (me, nodes', edges')

instance Pretty id => RPOCircuit Graph id where
    termGt t u = Graph $ do
                   n <- newNode
                   let me = (n, NTermGt (show$pPrint t) (show$pPrint u))
                   return (n, [me], [])
    termEq t u = Graph $ do
                   n <- newNode
                   let me = (n, NTermEq (show$pPrint t) (show$pPrint u))
                   return (n, [me], [])

--binaryNode :: NodeType v -> Graph v -> Graph v -> Graph v
{-# INLINE binaryNode #-}
binaryNode ty ledge redge l r = Graph $ do
        (lNode, lNodes, lEdges) <- unGraph l
        (rNode, rNodes, rEdges) <- unGraph r
        n <- newNode
        return (n, (n, ty) : lNodes ++ rNodes,
                   (lNode, n, ledge) : (rNode, n, redge) : lEdges ++ rEdges)

newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i


{-
defaultNodeAnnotate :: (Show v) => LNode (FrozenShared v) -> [GraphViz.Attribute]
defaultNodeAnnotate (_, FrozenShared (output, cmaps)) = go output
  where
    go CTrue{}       = "true"
    go CFalse{}      = "false"
    go (CVar _ i)    = show $ extract i varMap
    go (CNot{})      = "NOT"
    go (CAnd{hlc=h}) = maybe "AND" goHLC h
    go (COr{hlc=h})  = maybe "OR" goHLC h

    goHLC (Xor{})    = "XOR"
    goHLC (Onlyif{}) = go (output{ hlc=Nothing })
    goHLC (Iff{})    = "IFF"

    extract code f =
        IntMap.findWithDefault (error $ "shareGraph: unknown code: " ++ show code)
        code
        (f cmaps)

defaultEdgeAnnotate = undefined

dotGraph :: (Graph gr) => gr (FrozenShared v) (FrozenShared v) -> DotGraph
dotGraph g = graphToDot g defaultNodeAnnotate defaultEdgeAnnotate

-}

-- | Given a frozen shared circuit, construct a `G.DynGraph' that exactly
-- represents it.  Useful for debugging constraints generated as `Shared'
-- circuits.
shareGraph :: (G.DynGraph gr, Eq v, HasTrie v, Show v, Eq id, Pretty id, HasTrie id) =>
              FrozenShared id v -> gr (FrozenShared id v) (FrozenShared id v)
shareGraph (FrozenShared output cmaps) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c
    go c@(CIte i) = do (x, y, z) <- extract i iteMap
                       ( (cNode, cNodes, cEdges)
                        ,(tNode, tNodes, tEdges)
                        ,(eNode, eNodes, eEdges)) <- liftM3 (,,) (go x) (go y) (go z)
                       return (i, (i, frz c) : cNodes ++ tNodes ++ eNodes
                              ,(cNode, i, frz c)
                               : (tNode, i, frz c)
                               : (eNode, i, frz c)
                               : cEdges ++ tEdges ++ eEdges)

    go c@(CEq i) = extract i eqMap >>= tupM2 go >>= addKids c
    go c@(CLt i) = extract i ltMap >>= tupM2 go >>= addKids c
    go c@(CNat i) = return (i, [(i, frz c)], [])
    go c@(CFresh i) = return (i, [(i, frz c)], [])

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, frz ccode) : (rNode, i, frz ccode) : lEdges ++ rEdges)
    tupM2 f (x, y) = liftM2 (,) (f x) (f y)
    frz ccode = FrozenShared ccode cmaps
    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case BiTrie.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x


shareGraph' :: (G.DynGraph gr, Ord v, HasTrie v, Show v, Pretty id, Ord id) =>
              FrozenShared id v -> gr String String
shareGraph' (FrozenShared output cmaps) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c
    go c@(CIte i) = do (x, y, z) <- extract i iteMap
                       ( (cNode, cNodes, cEdges)
                        ,(tNode, tNodes, tEdges)
                        ,(eNode, eNodes, eEdges)) <- liftM3 (,,) (go x) (go y) (go z)
                       return (i, (i, frz c) : cNodes ++ tNodes ++ eNodes
                              ,(cNode, i, "if")
                               : (tNode, i, "then")
                               : (eNode, i, "else")
                               : cEdges ++ tEdges ++ eEdges)

    go c@(CEq i) = extract i eqMap >>= tupM2 go >>= addKids c
    go c@(CLt i) = extract i ltMap >>= tupM2 go >>= addKids c
    go c@(CNat i) = return (i, [(i, frz c)], [])
    go c@(CFresh i) = return (i, [(i, frz c)], [])
    go c@(COne i) = extract i oneMap >>= mapM go >>= addKidsOne i

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, "l") : (rNode, i, "r") : lEdges ++ rEdges)

    addKidsOne me tt = do
      let (tips, nodes, edges) = unzip3 tt
      let nodes' = (me, "ONE") : concat nodes
          edges' = [(n, me, "") | n <- tips ] ++ concat edges
      return (me, nodes', edges')


    tupM2 f (x, y) = liftM2 (,) (f x) (f y)

--    frz (CVar i) =  "v" ++ show i
    frz (CVar i) = show $ fromJust $ BiTrie.lookup i (varMap cmaps)
    frz CFalse{} = "false"
    frz CTrue{}  = "true"
    frz CNot{}   = "not"
    frz CAnd{} = "/\\"
    frz COr{}  = "\\/"
    frz CIff{} = "<->"
    frz COnlyif{} = "->"
    frz CXor{} = "xor"
    frz CIte{} = "if-then-else"
    frz (CNat c) = show c
    frz CEq{} = "=="
    frz CLt{} = "<"
    frz COne{} = "ONE"
    frz (CFresh i) = "v" ++ show i ++ "?"

    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case BiTrie.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x


-- | Returns an equivalent circuit with no iff, xor, onlyif, ite, nat, eq and lt nodes.
removeComplex :: (HasTrie id, Ord id, Ord v, HasTrie v, Show v, Circuit c) => FrozenShared id v -> c v
removeComplex c = go code
  where
  -- This first step removes the one constraints already
  FrozenShared code maps = runShared (castCircuit c) `asTypeOf` c
  freshAssigs   = Map.fromList [ (f, val)| (f@CFresh{}, val) <- BiTrie.elems(iffMap maps)]
  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren c (varMap maps)
--  go (CFresh i) = internalVar i
  go c@CFresh{} = maybe false go $
                  Map.lookup c freshAssigs
  go c@(COr{})  = uncurry or (go `onTup` getChildren c (orMap maps))
  go c@(CAnd{}) = uncurry and (go `onTup` getChildren c (andMap maps))

  go c@(CNot{}) = not . go $ getChildren c (notMap maps)
  go c@(CXor{}) = let
      (l, r) = go `onTup` getChildren c (xorMap maps)
      in (l `or` r) `and` not (l `and` r)
  go c@(COnlyif{}) = let
      (p, q) = go `onTup` getChildren c (onlyifMap maps)
      in not p `or` q
  go c@(CIff{}) = let
      (p, q) = go `onTup` getChildren c (iffMap maps)
      in iff p q
  go c@(CIte{}) = let
      (cc, tc, ec) = getChildren c (iteMap maps)
      [cond, t, e] = map go [cc, tc, ec]
      in ite cond t e
  go  CNat{} = typeError "removeComplex: expected a boolean."

  go c@CEq{}
      | (x@CNat{}, y@CNat{}) <- getChildren c (eqMap maps)
      , xx <- getChildren x (natMap maps)
      , yy <- getChildren y (natMap maps)
      = eq xx yy

      | otherwise
      = typeError "removeComplex: expected a boolean."

  go c@(CLt{})
      | (x@CNat{}, y@CNat{}) <- getChildren c (ltMap maps)
      , xx <- getChildren x (natMap maps)
      , yy <- getChildren y (natMap maps)
      = lt xx yy

      | otherwise
      = typeError "removeComplex: expected a boolean."

--  fresh = do { v:vv <- get; put vv; return (input v)}

  iff p q = (not p `or` q) `and` (not q `or` p)
  ite cond t e = (cond `and` t) `or` (not cond `and` e)

  eq (p:pp) (q:qq) =      (     (not (input p) `and` not (input q))
                           `or` (input p `and` input q)
                          )
                     `and` eq pp qq
  eq [] [] = true
  eq [] qq = not $ foldr or false $ map input qq
  eq pp [] = not $ foldr or false $ map input pp

  lt (p:pp) (q:qq) = lt pp qq `or` (not (input p) `and` input q `and` eq pp qq)
  lt [] [] = false
  lt [] qq = foldr or false $ map input qq
  lt _  [] = false

  onTup f (x, y) = (f x, f y)

--    -----------------------
-- ** Convert circuit to CNF
--    -----------------------

-- this data is private to toCNF.
data CNFResult = CP !Lit [Set Lit]
data CNFState = CNFS{ toCnfVars :: !([Var])
                      -- ^ infinite fresh var source, starting at 1
                    , toCnfMap  :: !(Var :<->: CCode)
                      -- ^ record var mapping
                    , toBitMap  :: !(Var :<->: (CCode,Int))
                    , numCnfClauses :: !Int
                    }

emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , numCnfClauses = 0
                    , toCnfMap = mempty
                    , toBitMap = mempty}

-- retrieve and create (if necessary) a cnf variable for the given ccode.
--findVar :: (MonadState CNFState m) => CCode -> m Lit
findVar ccode = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case BiTrie.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = BiTrie.insert v ccode m
                                    , toCnfVars = vs }
                    return . lit $ v
      Just v'  -> return . lit $ v'

findVar' ccode kfound knot = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case BiTrie.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = BiTrie.insert v ccode m
                                    , toCnfVars = vs }
                    knot $ lit v
      Just v'  -> kfound $ lit v'


recordVar ccode comp = do
    m <- gets toCnfMap
    case BiTrie.lookupR ccode m of
      Nothing -> do l <- comp
                    modify $ \s -> s{ toCnfMap = BiTrie.insert (var l) ccode (toCnfMap s) }
                    return l
      Just v  -> return (lit v)

-- | A circuit problem packages up the CNF corresponding to a given
-- `FrozenShared' circuit, and the mapping between the variables in the CNF and
-- the circuit elements of the circuit.

data RPOCircuitProblem id v = RPOCircuitProblem
    { rpoProblemCnf     :: CNFBS
    , rpoProblemCircuit :: !(FrozenShared id v)
    , rpoProblemCodeMap :: !(Var :<->: CCode)
    , rpoProblemBitMap  :: !(Var :<->: (CCode,Int)) }

removeComplex' :: (HasTrie id, Ord id, Ord v, HasTrie v, Show v, Circuit c) => FrozenShared id v -> c v
removeComplex' = ECircuit.removeComplex . ECircuit.runShared . removeComplex

toCNF :: (HasTrie id, Ord id, Ord v, HasTrie v, Show v) => FrozenShared id v -> CircuitProblem v
toCNF = ECircuit.toCNF . ECircuit.runShared . removeComplex

toCNFBS :: (HasTrie id, Ord id, Ord v, HasTrie v, Show v) => FrozenShared id v -> IO (ECircuitProblem v)
toCNFBS = ECircuit.toCNFBS . ECircuit.runShared . removeComplex

toCNFRPO :: (HasTrie id, Ord id, Ord v, HasTrie v, Show v, Show id) => FrozenShared id v -> IO(RPOCircuitProblem id v)
toCNFRPO c_in = do

    let !c@(FrozenShared !sharedCircuit !circuitMaps) = c_in
    tmp <- liftIO getTemporaryDirectory
    (tmpFile, h) <- liftIO $ openTempFile tmp "funsat.cnf"

    m <- ((`runReaderT` (circuitMaps, h)) . (`execStateT` emptyCNFState)) $ do
                     l <- toCNF' sharedCircuit
                     writeClauses [[l]]

    hClose h
    cnf <- BS.readFile tmpFile
    return $ RPOCircuitProblem
       { rpoProblemCnf = CNFBS { numVarsBS    = pred $ unVar $ head (toCnfVars m)
                               , numClausesBS = numCnfClauses m
                               , clausesBS    = cnf }
       , rpoProblemCircuit = c
       , rpoProblemCodeMap = toCnfMap m
       , rpoProblemBitMap  = toBitMap m}
  where
    debug msg = hPutStrLn stderr ("toCNFRpo - " ++ msg) >> hFlush stderr

    writeClauses cc =  do
        h <- asks snd
        incC (length cc)
        let bshow = BS.pack . show
        liftIO $ BS.hPut h $ BS.unlines $ map (\c -> BS.unwords (map bshow c ++ [BS.pack "0"])) cc

    -- Returns l where {l} U the accumulated c is CNF equisatisfiable with the input
    -- circuit.  Note that CNF conversion only has cases for And, Or, Not, True,
    -- False, and Var circuits.  We therefore remove the complex circuit before
    -- passing stuff to this function.
    toCNF' c@(CVar{})   = findVar' c goOn goOn
    toCNF' c@CFresh{}   = findVar' c goOn goOn

    toCNF' c@(CTrue{})  = true
    toCNF' c@(CFalse{}) = false
--     -- x <-> -y
--     --   <-> (-x, -y) & (y, x)
    toCNF' c@(CNot i) =  findVar' c goOn $ \notLit -> do
        eTree  <- extract i notMap
        eLit   <- toCNF' eTree
        writeClauses [  [negate notLit, negate eLit]
                     ,   [eLit, notLit]
                     ]
        return notLit

--     -- x <-> (y | z)
--     --   <-> (-y, x) & (-z, x) & (-x, y, z)
    toCNF' c@(COr i) = findVar' c goOn $ \orLit -> do
        (l, r) <- extract i orMap
        lLit <- toCNF' l
        rLit <- toCNF' r

        writeClauses [  [negate lLit, orLit]
                     ,  [negate rLit, orLit]
                     ,  [negate orLit, lLit, rLit]]

        return orLit

--     -- x <-> (y & z)
--     --   <-> (-x, y), (-x, z) & (-y, -z, x)
    toCNF' c@(CAnd i) = findVar' c goOn $ \andLit -> do
        (l, r) <- extract i andMap
        lLit <- toCNF' l
        rLit <- toCNF' r

        writeClauses [  [negate andLit, lLit]
                     ,  [negate andLit, rLit]
                     ,  [negate lLit, negate rLit, andLit]]

        return andLit

    toCNF' c@(CXor i) = recordVar c $ do
        (l,r) <- extract i xorMap
        lLit <- toCNF' l
        rLit <- toCNF' r
        (lLit `or` rLit) `andM` notM (lLit `and` rLit)

    toCNF' c@(COnlyif i) = recordVar c $ do
        (l,r) <- extract i onlyifMap
        lLit <- toCNF' l
        rLit <- toCNF' r
        (negate lLit `or` rLit)

    toCNF' c@(CIff i) = recordVar c $ do
        (l,r) <- extract i iffMap
        lLit <- toCNF' l
        rLit <- toCNF' r
        iff lLit rLit

    toCNF' c@(CIte i) = recordVar c $ do
        (c,t,e) <- extract i iteMap
        cLit <- toCNF' c
        tLit <- toCNF' t
        eLit <- toCNF' e
        ite cLit tLit eLit

    toCNF' c@(CEq i) = recordVar c $ do
        (nl,nr) <- extract i eqMap
        ll      <- findNat nl
        rr      <- findNat nr
        eq ll rr

    toCNF' c@(CLt i) = recordVar c $ do
        (nl,nr) <- extract i ltMap
        ll      <- findNat nl
        rr      <- findNat nr
        lt ll rr

    toCNF' c@(COne i) = recordVar c $ do
        cc      <- extract i oneMap
        case cc of
          [] -> false
          _  -> do
            vv      <- mapM toCNF' cc
            ones    <- replicateM (length vv) fresh
            zeros   <- replicateM (length vv) fresh
            f       <- false
            t       <- true
            writeClauses =<< mapM sequence
               [ [( return one_i  `iffM` ite b_i zero_i1 one_i1) `andM`
                    ( return zero_i `iffM` (negate b_i `and` zero_i1))]
                 | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                     zip5 vv ones zeros (tail ones ++ [f]) (tail zeros ++ [t])
               ]
            return (head ones)
      where
       zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee)
           = (a,b,c,d,e) : zip5 aa bb cc dd ee
       zip5 _ _ _ _ _ = []

    toCNF' c = do
        m <- asks fst
        error $  "toCNF' bug: unknown code: " ++ show c
              ++ " with maps:\n" ++ show (m{hashCount=[]})

    true = findVar' (CTrue trueHash) goOn $ \l -> do
        writeClauses [[l]]
        return l

    false = findVar' (CFalse falseHash) goOn $ \l -> do
        writeClauses  [ [negate l]]
        return l


    orM l r = do { vl <- l; vr <- r; or vl vr}
--    or lLit rLit | trace ("or " ++ show lLit ++ " " ++ show rLit) False = undefined
    or lLit rLit = do
        me <- fresh
        writeClauses [  [negate lLit, me]
                     ,  [negate rLit, me]
                     ,  [negate me, lLit, rLit]]

        return me

    andM l r = do { vl <- l; vr <- r; and vl vr}

--    and lLit rLit | trace ("and " ++ show lLit ++ " " ++ show rLit) False = undefined
    and lLit rLit =  do
        me <- fresh
        writeClauses [  [negate me, lLit]
                     ,  [negate me, rLit]
                     ,  [negate lLit, negate rLit,me]]

        return me

    notM = liftM negate

--    iff lLit rLit | trace ("iff " ++ show lLit ++ " " ++ show rLit) False = undefined
    iffM ml mr = do {l <- ml; r <- mr; iff l r}
    iff lLit rLit = (negate lLit `or` rLit) `andM` (negate rLit `or` lLit)
    ite cLit tLit eLit = (cLit `and` tLit) `orM` (negate cLit `and` eLit)

    eq [] []         = true
    eq [] rr         = notM $ foldr orM false (map return rr)
    eq ll []         = notM $ foldr orM false (map return ll)
    eq (l:ll) (r:rr) = iff l r `andM` eq ll rr

    lt [] []         = false
    lt _ []          = false
    lt [] rr         = foldr orM false $ map return rr
    lt (l:ll) (r:rr) = lt ll rr `orM` ((negate l `and` r) `andM` eq ll rr)

    incC i = modify $ \m ->  m{numCnfClauses = numCnfClauses m + i}

    extract code f = do
        m <- asks (f.fst)
        case BiTrie.lookup code m of
          Nothing -> error $ "toCNFRpo: unknown code: " ++ show code
          Just x  -> return x

    findNat c@(CNat ch) = do
        nm <- asks (natMap.fst)
        bm <- gets toBitMap
        vv <- gets toCnfVars
        case BiTrie.lookup ch nm of
          Nothing -> error $ "toCNFRpo: unknown nat code: " ++ show ch
          Just bits -> do
              let vars = mapM (\x -> BiTrie.lookupR x bm)
                              (zip (replicate (length bits) c) [0..])
              case vars of
                Just vv -> return (map lit vv)
                Nothing -> do
                  let bits' = take (length bits) vv
                  modify $ \s -> s{ toCnfVars = drop (length bits) vv
                                  , toBitMap  = foldr (\(b,i) -> BiTrie.insert b (CNat ch, i))
                                                  bm
                                                  (zip bits' [0..])
                              }
                  return (map lit bits')

    goOn c = return c

    fresh = do
       v:vs <- gets toCnfVars
       modify $ \s -> s{toCnfVars=vs}
       return (lit v)


projectRPOCircuitSolution sol prbl = case sol of
                                    Sat lits   -> projectLits lits
                                    Unsat lits -> projectLits lits
  where
  RPOCircuitProblem _ (FrozenShared _ maps) codeMap bitsMap = prbl
  projectLits lits =
      -- only the lits whose vars are (varMap maps) go to benv
      foldl (\m l -> case litHash l of
                       Var h   -> insertVar h l m
                       Bit h_i -> insertNat h_i l m
                       Auxiliar-> m)
            initiallyAllFalseMap
            (litAssignment lits)
    where

    initiallyAllFalseMap = Map.fromList
                           [(v,False) | v <- BiTrie.elems (varMap maps) ++ concat (BiTrie.elems (natMap maps))]

    insertVar h l m = case BiTrie.lookup h (varMap maps) of
                             Nothing -> m
                             Just v  -> Map.insert v (litSign l) m

    insertNat (h,i) l m = case BiTrie.lookup h (natMap maps) of
                          Nothing -> m
                          Just vv -> Map.insert (vv `safeAt` i) (litSign l) m

    litHash l = case BiTrie.lookup (var l) codeMap of
                  Nothing -> case BiTrie.lookup (var l) bitsMap of
                               Just (code,bit) -> Bit (circuitHash code, bit)
                               Nothing    -> Auxiliar
                  Just code -> Var (circuitHash code)

    safeAt l i = CE.assert (i < length l) (l !! i)
data ProjectionCase = Var CircuitHash | Bit (CircuitHash, Int) | Auxiliar

-- ------------------------
-- HasTrie instances
-- ------------------------

instance HasTrie Var where
  newtype Var :->: x = VarTrie (Int :->: x)
  empty = VarTrie Trie.empty
  lookup (V i) (VarTrie t) = Trie.lookup i t
  insert (V i) v (VarTrie t) = VarTrie (Trie.insert i v t)
  toList (VarTrie t) = map (first V) (Trie.toList t)

-- -------
-- Errors
-- -------

typeError :: String -> a
typeError msg = error (msg ++ "\nPlease send an email to the pepeiborra@gmail.com requesting a typed circuit language.")


