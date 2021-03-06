{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-| Extension of Funsat.Circuit to generate RPO constraints as boolean circuits

-}
module Narradar.Constraints.SAT.RPOCircuit
   (Circuit(..)
   ,ECircuit(..)
   ,NatCircuit(..)
   ,OneCircuit(..), oneDefault, oneExist
   ,RPOCircuit(..), termGt_, termGe_, termEq_
   ,RPOExtCircuit(..)
   ,ExistCircuit(..)
   ,AssertCircuit(..), assertCircuits
   ,CastCircuit(..), CastRPOCircuit(..)
   ,HasPrecedence(..), precedence
   ,HasFiltering(..), listAF, inAF
   ,HasStatus(..), useMul, lexPerm
   ,Shared(..), FrozenShared(..), runShared
   ,EvalM, Eval, EvalF(..), BEnv, BIEnv
   ,runEval, runEvalM, evalB, evalN
   ,Graph(..), shareGraph, shareGraph'
   ,Tree(..), simplifyTree, printTree, mapTreeTerms
   ,ECircuitProblem(..), RPOCircuitProblem(..)
   ,CNF(..)
   ,removeComplex, removeExist
   ,toCNF, toCNF'
   ,projectECircuitSolution, projectRPOCircuitSolution
   ,reconstructNatsFromBits
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
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State.Strict hiding ((>=>), forM_)
import Data.Bimap( Bimap )
import Data.ByteString.Lazy.Char8 (ByteString)
import Data.Foldable (Foldable, foldMap)
import Data.List( nub, foldl', sortBy, (\\))
import Data.Map( Map )
import Data.Maybe( fromJust )
import Data.Hashable
import Data.Monoid
import Data.Set( Set )
import Data.Traversable (Traversable, traverse, fmapDefault, foldMapDefault)
import Prelude hiding( not, and, or, (>) )

import Funsat.ECircuit ( Circuit(..)
                       , ECircuit(..)
                       , NatCircuit(..)
                       , ExistCircuit(..)
                       , CastCircuit(..)
                       , CircuitHash, falseHash, trueHash
                       , Eval, EvalF(..), BEnv, BIEnv, runEval, fromBinary
                       , ECircuitProblem(..)
                       , projectECircuitSolution, reconstructNatsFromBits)
import Funsat.Types( CNF(..), Lit(..), Var(..), var, lit, Solution(..), litSign, litAssignment )

import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types hiding (Var,V,var,fresh)
import Narradar.Utils ( chunks, selectSafe, safeAtL, on )

import System.Directory (getTemporaryDirectory)
import System.FilePath
import System.IO


import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import qualified Data.Bimap as Bimap
import qualified Funsat.Circuit  as Circuit
import qualified Funsat.ECircuit as ECircuit
import qualified Prelude as Prelude
import qualified Data.HashMap as HashMap

type k :->:  v = HashMap.HashMap k v
type k :<->: v = Bimap.Bimap k v

class Circuit repr => OneCircuit repr where
    -- | @one bb = length (filter id bb) == 1@
    one  :: (Ord var, Show var) => [repr var] -> repr var
    one  = oneDefault

oneExist :: (Ord v, Show v, ECircuit repr, ExistCircuit repr) => [repr v] -> repr v
oneExist [] = false
oneExist vv = (`runCont` id) $ do
          ones  <- replicateM (length vv) (cont exists)
          zeros <- replicateM (length vv) (cont exists)
          let encoding = andL
                  [ (one_i  `iff` ite b_i zero_i1 one_i1) `and`
                    ( zero_i `iff` (not b_i `and` zero_i1))
                   | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                      zip5 vv ones zeros (tail ones ++ [false]) (tail zeros ++ [true])
                  ]
          return (head ones `and` encoding)
      where
       zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee)
           = (a,b,c,d,e) : zip5 aa bb cc dd ee
       zip5 _ _ _ _ _ = []

oneDefault :: (Ord v, Show v, Circuit repr) => [repr v] -> repr v
oneDefault [] = false
oneDefault (v:vv) = (v `and` none vv) `or` (not v `and` oneDefault vv)
  where
   none = foldr and true . map not

class NatCircuit repr => RPOCircuit repr tid tvar | repr -> tid tvar where
    termGt, termGe, termEq :: (HasPrecedence v tid, HasFiltering v tid, HasStatus v tid
                              ,Ord v, Show v, Hashable v
                              ,Eq tvar, Pretty tvar, Show tvar, Hashable tvar, Ord tvar) =>
                              Term (TermF tid) tvar -> Term (TermF tid) tvar -> repr v
    termGe s t = termGt s t `or` termEq s t

class RPOCircuit repr tid tvar => RPOExtCircuit repr tid tvar where
    exGt, exGe, exEq :: (HasPrecedence v tid, HasFiltering v tid, HasStatus v tid
                        ,Ord v, Hashable v, Show v) =>
                        tid -> tid -> [Term (TermF tid) tvar] -> [Term (TermF tid) tvar] -> repr v
    exGe id_s id_t ss tt = exGt id_s id_t ss tt `or` exEq id_s id_t ss tt

class AssertCircuit repr where
  assertCircuit :: repr v  -- * Assertion side-effect
                -> repr v  -- * expression
                -> repr v  -- * expression

assertCircuits [] e = e
assertCircuits (a:aa) e = assertCircuit a $ assertCircuits aa e

class HasPrecedence v a | a -> v where precedence_v  :: a -> v
class HasFiltering  v a | a -> v where listAF_v      :: a -> v
                                       filtering_vv  :: a -> [v]
class HasStatus v id | id -> v   where useMul_v      :: id -> v
                                       lexPerm_vv    :: id -> Maybe [[v]]

precedence :: (NatCircuit repr, HasPrecedence v id, Ord v, Hashable v, Show v) => id -> repr v
precedence = nat . precedence_v
listAF :: (Circuit repr, HasFiltering v id, Ord v, Hashable v, Show v) => id -> repr v
listAF     = input . listAF_v
{-# INLINE inAF #-}
inAF   :: (Circuit repr, HasFiltering v id, Ord v, Hashable v, Show v) => Int -> id -> repr v
inAF i     = input . (!! pred i) . filtering_vv
useMul :: (Circuit repr, HasStatus v id, Ord v, Hashable v, Show v) => id -> repr v
useMul     = input . useMul_v
lexPerm :: (Circuit repr, HasStatus v id, Ord v, Hashable v, Show v) => id -> Maybe [[repr v]]
lexPerm    = (fmap.fmap.fmap) input . lexPerm_vv

termGt_, termEq_, termGe_ ::
        (Hashable id, Ord id, HasStatus var id, HasPrecedence var id, HasFiltering var id
        ,Ord var, Hashable var, Show var
        ,Eq tvar, Ord tvar, Hashable tvar, Show tvar, Pretty tvar 
        ,ECircuit repr, RPOExtCircuit repr id tvar) =>
        Term (TermF id) tvar -> Term (TermF id) tvar -> repr var

termGt_ s t
    | s == t = false

    | Just id_t <- rootSymbol t
    , Just id_s <- rootSymbol s
    = cond1 id_s id_t tt_s tt_t `or` cond2 id_s tt_s

    | Just id_s <- rootSymbol s
    = cond2 id_s tt_s

    | otherwise = false
   where
    tt_s = directSubterms s
    tt_t = directSubterms t

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

    all f = andL . map f
    any f = orL  . map f

    infixr 8 >
    infixr 8 ~~
    infixr 7 -->

    s > t   = termGt s t
    s ~~ t  = termEq s t
    a --> b = onlyif a b

termGe_ (Pure s) (Pure t) = if s == t then true else false
termGe_ s t
   | s == t  = true
   | isVar s = not(listAF id_t) `and`
               all (\(t_j,j) -> inAF j id_t --> s ~~ t_j)
                   (zip tt [1..])

   | Just id_s <- rootSymbol s
   , isVar t = ite (listAF id_s)
                   (any (\(s_i,i) -> inAF i id_s /\  s_i >~ t) (zip ss [1..]))
                   (all (\(s_i,i) -> inAF i id_s --> s_i >~ t) (zip ss [1..]))

   | id_s == id_t
   = ite (listAF id_s)
         (exGe id_s id_t ss tt)
         (all (\(s_i,t_i,i) -> inAF i id_s --> s_i >~ t_i) (zip3 ss tt [1..]))

   | otherwise
   = ite (listAF id_s)
         (ite (listAF id_t)
              ((precedence id_s `eq` precedence id_t) `and` exGe id_s id_t ss tt)
              (all (\(t_j,j) -> inAF j id_t --> s >~ t_j) (zip tt [1..])))
         (all (\(s_i,i) -> inAF i id_s --> s_i >~ t) (zip ss [1..]))
  where
    ss = directSubterms s
    tt = directSubterms t
    ~(Just id_s) = rootSymbol s
    ~(Just id_t) = rootSymbol t

    all f = andL . map f
    any f = orL  . map f

    infixr 8 /\, >, >~, ~~
    infixr 7 -->

    s > t   = termGt s t
    s >~ t  = termGe s t
    s ~~ t  = termEq s t
    a /\  b = a `and` b
    a --> b = onlyif a b

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
              (all (\(t_j,j) -> inAF j id_t --> s ~~ t_j) (zip tt [1..])))
         (all (\(s_i,i) -> inAF i id_s --> s_i ~~ t) (zip ss [1..]))

   where
    ss = directSubterms s
    tt = directSubterms t
    ~(Just id_s) = rootSymbol s
    ~(Just id_t) = rootSymbol t

    all f = andL . map f
    any f = orL  . map f

    infixr 8 >
    infixr 8 ~~
    infixr 7 -->

    s > t   = termGt s t
    s ~~ t  = termEq s t
    a --> b = onlyif a b


class CastRPOCircuit c cOut tid tvar | c -> tid tvar where
  castRPOCircuit :: ( HasPrecedence v tid, HasFiltering v tid, HasStatus v tid
                    , Ord v, Hashable v, Show v
                    , Hashable tid, Ord tid
                    , Hashable tvar, Ord tvar, Show tvar, Pretty tvar) =>
                    c v -> cOut v

instance CastCircuit Circuit.Tree c => CastRPOCircuit Circuit.Tree c id var where
    castRPOCircuit = castCircuit
instance CastCircuit ECircuit.Tree c => CastRPOCircuit ECircuit.Tree c id var where
    castRPOCircuit = castCircuit

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShared'.
newtype Shared tid tvar var = Shared { unShared :: State (CMaps tid tvar var) CCode }

-- | A shared circuit that has already been constructed.
data FrozenShared tid tvar var = FrozenShared !CCode !(CMaps tid tvar var) deriving Eq

frozenShared code maps = FrozenShared code maps


instance (Hashable id, Show id, Hashable tvar, Show tvar, Hashable var, Show var) => Show (FrozenShared id tvar var) where
  showsPrec p (FrozenShared c maps) = ("FrozenShared " ++) . showsPrec p c . showsPrec p maps{hashCount=[]}


-- | Reify a sharing circuit.
runShared :: (Hashable id, Ord id, Hashable tvar, Ord tvar) => Shared id tvar var -> FrozenShared id tvar var
runShared = runShared' emptyCMaps

runShared' :: (Hashable id, Ord id, Hashable tvar, Ord tvar) => CMaps id tvar var -> Shared id tvar var -> FrozenShared id tvar var
runShared' maps = uncurry frozenShared . (`runState` emptyCMaps) . unShared

getChildren :: (Ord v, Hashable v) => CCode -> CircuitHash :<->: v -> v
getChildren code codeMap =
    case Bimap.lookup (circuitHash code) codeMap of
      Nothing -> findError
      Just c  -> c
  where findError = error $ "getChildren: unknown code: " ++ show code

getChildren' :: (Ord v) => CCode -> Bimap CircuitHash v -> v
getChildren' code codeMap =
    case Bimap.lookup (circuitHash code) codeMap of
      Nothing -> findError
      Just c  -> c
  where findError = error $ "getChildren: unknown code: " ++ show code

instance (Hashable id, Ord id, Hashable tvar, Ord tvar, ECircuit c, NatCircuit c, ExistCircuit c) => CastCircuit (Shared id tvar) c where
    castCircuit = castCircuit . runShared

instance (ECircuit c, NatCircuit c, ExistCircuit c) => CastCircuit (FrozenShared id tvar) c where
    castCircuit (FrozenShared code maps) = runCont (go code) id
      where
        go (CTrue{})     = return true
        go (CFalse{})    = return false
        go (CExist c)    = cont exists
        go c@(CVar{})    = return $ input $ getChildren' c (varMap maps)
        go c@(CAnd{})    = liftM(uncurry and)     . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = liftM(uncurry or)      . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = liftM not              . go  $ getChildren c (notMap maps)
        go c@(CXor{})    = liftM (uncurry xor)    . go2 $ getChildren c (xorMap maps)
        go c@(COnlyif{}) = liftM (uncurry onlyif) . go2 $ getChildren c (onlyifMap maps)
        go c@(CIff{})    = liftM (uncurry iff)    . go2 $ getChildren c (iffMap maps)
        go c@(CIte{})    = liftM (uncurry3 ite)   . go3 $ getChildren c (iteMap maps)
        go c@CEq{}       = liftM (uncurry eq)     . go2 $ getChildren c (eqMap maps)
        go c@CLt{}       = liftM (uncurry lt)     . go2 $ getChildren c (ltMap maps)
        go c@CNat{}      = return $ nat $ getChildren' c (natMap maps)
        go c@COne{}      = liftM oneDefault $ mapM go $ getChildren c (oneMap maps)

        go2 (a,b)   = do {a' <- go a; b' <- go b; return (a',b')}
        go3 (a,b,c) = do {a' <- go a; b' <- go b; c' <- go c; return (a',b',c')}
        uncurry3 f (x, y, z) = f x y z

instance (Hashable id, Ord id, ECircuit c, NatCircuit c, ExistCircuit c) => CastRPOCircuit (Shared id var) c id var where
    castRPOCircuit = castCircuit

instance (ECircuit c, NatCircuit c, ExistCircuit c) => CastRPOCircuit (FrozenShared id var) c id var where
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
              | CExist  { circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show, Read)

instance Hashable CCode where hash = circuitHash

-- | Maps used to implement the common-subexpression sharing implementation of
-- the `Circuit' class.  See `Shared'.
data CMaps tid tvar v = CMaps
    { hashCount :: ![CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.  Should not
    -- include 0 or 1.

    , varMap    :: !(Bimap CircuitHash v)
     -- ^ Mapping of generated integer IDs to variables.
    , freshSet  :: !(Set CircuitHash)
    , andMap    :: !(CircuitHash :<->: (CCode, CCode))
    , orMap     :: !(CircuitHash :<->: (CCode, CCode))
    , notMap    :: !(CircuitHash :<->: CCode)
    , xorMap    :: !(CircuitHash :<->: (CCode, CCode))
    , onlyifMap :: !(CircuitHash :<->: (CCode, CCode))
    , iffMap    :: !(CircuitHash :<->: (CCode, CCode))
    , iteMap    :: !(CircuitHash :<->: (CCode, CCode, CCode))
    , natMap    :: !(CircuitHash :<->: v)
    , eqMap     :: !(CircuitHash :<->: (CCode, CCode))
    , ltMap     :: !(CircuitHash :<->: (CCode, CCode))
    , oneMap    :: !(CircuitHash :<->: [CCode])
    , termGtMap :: !((Term (TermF tid) tvar, Term (TermF tid) tvar) :->: CCode)
    , termGeMap :: !((Term (TermF tid) tvar, Term (TermF tid) tvar) :->: CCode)
    , termEqMap :: !((Term (TermF tid) tvar, Term (TermF tid) tvar) :->: CCode)
    }

deriving instance (Hashable id, Show id, Hashable var, Show var, Hashable tvar, Show tvar) => Show (CMaps id tvar var)
deriving instance (Eq id, Hashable id, Eq var, Hashable var, Eq tvar, Hashable tvar) => Eq (CMaps id tvar var)


-- | A `CMaps' with an initial `hashCount' of 2.
emptyCMaps :: (Hashable id, Ord id, Ord tvar, Hashable tvar) => CMaps id tvar var
emptyCMaps = CMaps
    { hashCount = [2 ..]
    , varMap    = Bimap.empty
    , freshSet  = Set.empty
    , andMap    = Bimap.empty
    , orMap     = Bimap.empty
    , notMap    = Bimap.empty
    , xorMap    = Bimap.empty
    , onlyifMap = Bimap.empty
    , iffMap    = Bimap.empty
    , iteMap    = Bimap.empty
    , natMap    = Bimap.empty
    , eqMap     = Bimap.empty
    , ltMap     = Bimap.empty
    , oneMap    = Bimap.empty
    , termGtMap = mempty
    , termGeMap = mempty
    , termEqMap = mempty
    }

-- prj: "projects relevant map out of state"
-- upd: "stores new map back in state"
{-# INLINE recordC #-}
recordC :: (Ord a, Hashable a) =>
           (CircuitHash -> b)
        -> (CMaps id tvar var -> Int :<->: a)            -- ^ prj
        -> (CMaps id tvar var -> Int :<->: a -> CMaps id tvar var) -- ^ upd
        -> a
        -> State (CMaps id tvar var) b
recordC _ _ _ x | x `seq` False = undefined
recordC cons prj upd x = do
  s <- get
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (Bimap.insert c x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ Bimap.lookupR x (prj s)

{-# INLINE recordC' #-}
recordC' :: Ord a =>
           (CircuitHash -> b)
        -> (CMaps id tvar var  -> Bimap Int a)            -- ^ prj
        -> (CMaps id tvar var -> Bimap Int a -> CMaps id tvar var) -- ^ upd
        -> a
        -> State (CMaps id tvar var) b
recordC' _ _ _ x | x `seq` False = undefined
recordC' cons prj upd x = do
  s <- get
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (Bimap.insert c x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ Bimap.lookupR x (prj s)


instance Circuit (Shared id tvar) where
    false = Shared falseS
    true  = Shared trueS
    input v = Shared $ recordC' CVar varMap (\s e -> s{ varMap = e }) v
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


instance ExistCircuit (Shared id tvar) where
    exists k  = Shared $ do
        c:cs <- gets hashCount
        modify $ \s -> s{freshSet = Set.insert c (freshSet s), hashCount=cs}
        unShared . k . Shared . return . CExist $ c

instance ECircuit (Shared id tvar) where
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

falseS, trueS :: State (CMaps id tvar var) CCode
falseS = return $ CFalse falseHash
trueS  = return $ CTrue trueHash

notS CTrue{}  = falseS
notS CFalse{} = trueS
notS (CNot i) = do {s <- get; return $ fromJust $ Bimap.lookup i (notMap s) }
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

instance OneCircuit (Shared id tvar) where
    one ss = Shared $ do
               xx <- sequence $ map unShared ss
               if null xx then falseS else recordC COne oneMap (\s e' -> s{oneMap = e'}) xx

instance NatCircuit (Shared id tvar) where
    eq xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 if x == y then trueS else recordC CEq eqMap (\s e -> s {eqMap = e}) (x,y)

    lt xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 if x == y then falseS else recordC CLt ltMap (\s e -> s {ltMap = e}) (x,y)

    nat = Shared . recordC' CNat natMap (\s e -> s{ natMap = e })

instance (Ord tid, Hashable tid, RPOExtCircuit (Shared tid tvar) tid tvar) =>
    RPOCircuit (Shared tid tvar) tid tvar where
 termGt s t = Shared $ do
      env <- get
      case HashMap.lookup (s,t) (termGtMap env) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termGt_ s t
           modify $ \env -> env{termGtMap = HashMap.insert (s,t) me (termGtMap env)}
           return me
 termEq s t = Shared $ do
      env <- get
      case (HashMap.lookup (s,t) (termEqMap env)) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termEq_ s t
           modify $ \env -> env{termEqMap = HashMap.insert (s,t) me (termEqMap env)}
           return me
 termGe s t = Shared $ do
      env <- get
      case (HashMap.lookup (s,t) (termGeMap env)) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termGe_ s t
           modify $ \env -> env{termGeMap = HashMap.insert (s,t) me (termGeMap env)}
           return me

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.

data TreeF term (a :: *)
               = TTrue
               | TFalse
               | TNot a
               | TAnd a a
               | TOr  a a
               | TXor a a
               | TIff a a
               | TOnlyIf a a
               | TIte a a a
               | TEq  a a
               | TLt  a a
               | TOne [a]
               | TTermEq term term
               | TTermGt term term
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)



type Tree id var = Tree' (Term (TermF id) var)
data Tree' term v = TNat v
                  | TLeaf v
                  | TFix {tfix :: TreeF term (Tree' term v)}
  deriving (Eq, Ord, Show)

tLeaf   = TLeaf
tNat    = TNat
tTrue   = TFix TTrue
tFalse  = TFix TFalse
tNot    = TFix . TNot
tOne    = TFix . TOne
tAnd    = (TFix.) . TAnd
tOr     = (TFix.) . TOr
tXor    = (TFix.) . TXor
tIff    = (TFix.) . TIff
tOnlyIf = (TFix.) . TOnlyIf
tEq     = (TFix.) . TEq
tLt     = (TFix.) . TLt
tIte    = ((TFix.).) . TIte
tTermGt = (TFix.) . TTermGt
tTermEq = (TFix.) . TTermEq

tOpen (TFix t) = Just t
tOpen _ = Nothing

tClose = TFix

tId TTrue  = tTrue
tId TFalse = tFalse
tId (TNot n) = tNot n
tId (TOne n) = tOne n
tId (TAnd t1 t2) = tAnd t1 t2
tId (TOr  t1 t2) = tOr t1 t2
tId (TXor t1 t2) = tXor t1 t2
tId (TIff t1 t2) = tIff t1 t2
tId (TOnlyIf t1 t2) = tOnlyIf t1 t2
tId (TEq t1 t2) = tEq t1 t2
tId (TLt t1 t2) = tLt t1 t2
tId (TIte c t e) = tIte c t e

foldTree fnat  _ _ (TNat v)  = fnat v
foldTree _ fleaf _ (TLeaf v) = fleaf v
foldTree fn fl f (TFix t) = f (fmap (foldTree fn fl f) t)

mapTreeTerms :: (Term (TermF id) var -> Term (TermF id') var') -> Tree id var v -> Tree id' var' v
mapTreeTerms f = foldTree tNat tLeaf f'
  where
   f' (TTermGt t u) = tTermGt (f t) (f u)
   f' (TTermEq t u) = tTermGt (f t) (f u)
   f' t = tId t

printTree :: (Pretty id, Pretty v, Pretty var) => Int -> Tree id var v -> Doc
printTree p t = foldTree fn fl f t p where
  fl v _ = pPrint v
  fn v _ = pPrint v
  f TTrue  _ = text "true"
  f TFalse _ = text "false"
  f (TNot t)        p = pP p 9 $ text "!" <> t 9
  f (TAnd t1 t2)    p = pP p 5 $ text "AND" <+> (t1 5 $$ t2 5)
--   f (TAnd t1 t2) p = pP p 5 $ pt 5 t1 <+> text "&" <+> pt 5 t2
  f (TOr t1 t2)     p = pP p 5 $ text "OR " <+> (t1 5 $$ t2 5)
--   f (TOr  t1 t2) p = pP p 5 $ t1 5 <+> text "||" <+> pt 5 t2
  f (TXor t1 t2)    p = pP p 5 $ t1 5 <+> text "xor" <+> t2 5
  f (TIff t1 t2)    p = pP p 3 $ t1 3 <+> text "<->" <+> t2 3
  f (TOnlyIf t1 t2) p = pP p 3 $ t1 3 <+> text "-->" <+> t2 3
  f (TIte c t e)    p = pP p 2 $ text "IFTE" <+> (c 1 $$ t 1 $$ e 1)
  f (TEq n1 n2)     p = pP p 7 (n1 1 <+> text "==" <+> n2 1)
  f (TLt n1 n2)     p = pP p 7 (n1 1 <+> text "<"  <+> n2 1)
  f (TOne vv)       p = pP p 1 $ text "ONE" <+> (fsep $ punctuate comma $ map ($ 1) vv)
  f (TTermGt t u)   p = pP p 6 $ pPrint t <+> text ">" <+> pPrint u
  f (TTermEq t u)   p = pP p 6 $ pPrint t <+> text "=" <+> pPrint u

pP prec myPrec doc = if myPrec Prelude.> prec then doc else parens doc

collectIdsTree :: Ord id => Tree id var v -> Set id
collectIdsTree = foldTree (const mempty) (const mempty) f
  where
   f (TNot t1)       = t1
   f (TAnd t1 t2)    = mappend t1 t2
   f (TOr t1 t2)     = mappend t1 t2
   f (TXor t1 t2)    = mappend t1 t2
   f (TOnlyIf t1 t2) = mappend t1 t2
   f (TIff t1 t2)    = mappend t1 t2
   f (TIte t1 t2 t3) = t1 `mappend` t2 `mappend` t3
   f (TTermGt t1 t2) = Set.fromList (collectIds t1) `mappend` Set.fromList (collectIds t2)
   f (TTermEq t1 t2) = Set.fromList (collectIds t1) `mappend` Set.fromList (collectIds t2)
   f TOne{} = mempty
   f TTrue  = mempty
   f TFalse = mempty

-- | Performs obvious constant propagations.
simplifyTree :: (Eq var, Eq v, Eq id) => Tree id var v -> Tree id var v
simplifyTree = foldTree TNat TLeaf f where
  f TFalse      = tFalse
  f TTrue       = tTrue

  f (TNot (tOpen -> Just TTrue))  = tFalse
  f (TNot (tOpen -> Just TFalse)) = tTrue
  f it@(TNot t) = tClose it

  f (TAnd (tOpen -> Just TFalse) _) = tFalse
  f (TAnd (tOpen -> Just TTrue) r)  = r
  f (TAnd l (tOpen -> Just TTrue))  = l
  f (TAnd _ (tOpen -> Just TFalse)) = tFalse
  f it@TAnd{} = tClose it

  f (TOr (tOpen -> Just TTrue) _) = tTrue
  f (TOr (tOpen -> Just TFalse) r) = r
  f (TOr _ (tOpen -> Just TTrue)) = tTrue
  f (TOr l (tOpen -> Just TFalse)) = l
  f it@TOr{} = tClose it

  f (TXor (tOpen -> Just TTrue) (tOpen -> Just TTrue)) = tFalse
  f (TXor (tOpen -> Just TFalse) r) = r
  f (TXor l (tOpen -> Just TFalse)) = l
  f (TXor (tOpen -> Just TTrue) r) = tNot r
  f (TXor l (tOpen -> Just TTrue)) = tNot l
  f it@TXor{} = tClose it

  f (TIff (tOpen -> Just TFalse) (tOpen -> Just TFalse)) = tTrue
  f (TIff (tOpen -> Just TFalse) r) = tNot r
  f (TIff (tOpen -> Just TTrue)  r) = r
  f (TIff l (tOpen -> Just TFalse)) = tNot l
  f (TIff l (tOpen -> Just TTrue))  = l
  f it@TIff{} = tClose it

  f it@(l `TOnlyIf` r) =
    case (tOpen l, tOpen r) of
         (Just TFalse,_)  -> tTrue
         (Just TTrue,_)   -> r
         (_, Just TTrue)  -> tTrue
         (_, Just TFalse) -> tNot l
         _           -> tClose it
  f it@(TIte x t e) =
    case (tOpen x, tOpen t, tOpen e) of
         (Just TTrue,_,_)  -> t
         (Just TFalse,_,_) -> e
         (_,Just TTrue,_)  -> tOr x e
         (_,Just TFalse,_) -> tAnd (tNot x) e
         (_,_,Just TTrue)  -> tOr (tNot x) t
         (_,_,Just TFalse) -> tAnd x t
         _      -> tClose it

  f t@(TEq x y) = if x == y then tTrue  else tClose t
  f t@(TLt x y) = if x == y then tFalse else tClose t
  f (TOne [])   = tFalse
  f t@TOne{}    = tClose t
  f (TTermEq s t) | s == t = tTrue
  f t@TTermEq{} = tClose t
  f (TTermGt s t) | s == t = tFalse
  f t@TTermGt{} = tClose t

instance (ECircuit c, NatCircuit c, OneCircuit c) =>
  CastCircuit (Tree id var) c
 where
  castCircuit = foldTree input nat f where
    f TTrue        = true
    f TFalse       = false
    f (TAnd t1 t2) = and t1 t2
    f (TOr t1 t2)  = or  t1 t2
    f (TXor t1 t2) = xor t1 t2
    f (TNot t)     = not t
    f (TIff t1 t2) = iff t1 t2
    f (TOnlyIf t1 t2) = onlyif t1 t2
    f (TIte x t e) = ite x t e
    f (TEq t1 t2)  = eq t1 t2
    f (TLt t1 t2)  = lt t1 t2
    f (TOne tt)    = one tt
    f c@(TTermEq t u) = error "cannot cast RPO constraints"
    f c@(TTermGt t u) = error "cannot cast RPO constraints"

instance (ECircuit c, NatCircuit c, OneCircuit c, RPOCircuit c tid tvar) =>
  CastRPOCircuit (Tree tid tvar) c tid tvar
 where
  castRPOCircuit = foldTree input nat f where
    f TTrue        = true
    f TFalse       = false
    f (TAnd t1 t2) = and t1 t2
    f (TOr t1 t2)  = or  t1 t2
    f (TXor t1 t2) = xor t1 t2
    f (TNot t)     = not t
    f (TIff t1 t2) = iff t1 t2
    f (TOnlyIf t1 t2) = onlyif t1 t2
    f (TIte x t e) = ite x t e
    f (TEq t1 t2)  = eq t1 t2
    f (TLt t1 t2)  = lt t1 t2
    f (TOne tt)    = one tt
    f c@(TTermEq t u) = termEq t u
    f c@(TTermGt t u) = termGt t u

instance Circuit (Tree id var) where
    true  = tTrue
    false = tFalse
    input = tLeaf
    and   = tAnd
    or    = tOr
    not   = tNot

instance ECircuit (Tree id var) where
    xor    = tXor
    iff    = tIff
    onlyif = tOnlyIf
    ite    = tIte

instance NatCircuit (Tree id var) where
    eq    = tEq
    lt    = tLt
    nat   = TNat

instance OneCircuit (Tree id var) where
    one   = tOne

instance RPOCircuit (Tree id var) id var where
    termGt = tTermGt
    termEq = tTermEq

--    ------------------
-- ** Circuit evaluator
--    ------------------
newtype Flip t a b = Flip {unFlip::t b a}
type EvalM = Flip EvalF

fromLeft :: Either l r -> l
fromLeft (Left l) = l
fromRight :: Either l r -> r
fromRight (Right r) = r

runEvalM :: BIEnv e -> EvalM e a -> a
runEvalM env = flip unEval env . unFlip

instance Functor (EvalM v) where fmap f (Flip (Eval m)) = Flip $ Eval $ \env -> f(m env)
instance Monad (EvalM v) where
  return x = Flip $ Eval $ \_ -> x
  m >>= f  = Flip $ Eval $ \env -> runEvalM env $ f $ runEvalM env m

instance MonadReader (BIEnv v) (EvalM v) where
  ask       = Flip $ Eval $ \env -> env
  local f m = Flip $ Eval $ \env -> runEvalM (f env) m

instance OneCircuit Eval where
  one tt    = Eval (\env -> Right $ case filter id $  map (fromRight . (`unEval` env)) tt of
                                        (_:[]) -> True
                                        _      -> False)

instance (Ord id) => RPOCircuit Eval id var
  where
   termGt t u = unFlip (Right `liftM` (>)  evalRPO t u)
   termEq t u = unFlip (Right `liftM` (~~) evalRPO t u)

data RPOEval v a = RPO {(>), (>~), (~~) :: a -> a -> Flip EvalF v Bool}

evalB :: Eval v -> EvalM v Bool
evalN :: Eval v -> EvalM v Int
evalB c = liftM (fromRight :: Either Int Bool -> Bool) (eval c)
evalN c = liftM (fromLeft  :: Either Int Bool -> Int)  (eval c)
eval  c = do {env <- ask; return (runEval env c)}

evalRPO :: forall id v var.
           (Eq id, Ord id, HasPrecedence v id, HasStatus v id, HasFiltering v id
           ,Ord v, Hashable v, Show v
           ,Eq var
           ) => RPOEval v (Term (TermF id) var)
evalRPO = RPO{..} where

  infixr 4 >
  infixr 4 >~
  infixr 4 ~~

  s >~ t = s > t <|> s ~~ t

  s ~~ t
   | s == t = return True

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , id_s == id_t
   = do
     af_s <- compFiltering id_s
     case af_s of
      Left i -> (tt_s !! pred i) ~~ t
      _      -> exeq s t

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t
   = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s,af_t) of
      (Left i, _) -> safeAtL "RPOCircuit:928" tt_s (pred i) ~~ t
      (_, Left j) -> s ~~ safeAtL "RPOCircuit:929" tt_t (pred j)
      (_,_) -> evalB (precedence id_s `eq` precedence id_t) <&> exeq s t

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     case af_s of
      Left i-> safeAtL "RPOCircuit:935" tt_s (pred i) ~~ t
      _     -> return False

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t = do
     af_t <- compFiltering id_t
     case af_t of
      Left j -> s ~~ safeAtL "RPOCircuit:941" tt_t (pred j)
      _      -> return False

   | otherwise = return False

  s > t

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , id_s == id_t
   = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s, af_t) of
      (Left i, _) -> safeAtL "RPOCircuit:955" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "RPOCircuit:956" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> exgt s t)
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s, af_t) of
      (Left i, Left j) -> safeAtL "RPOCircuit:698" tt_s (pred i) > safeAtL "RPOCircuit:698" tt_t (pred j)
      (Left i, _) -> safeAtL "RPOCircuit:698" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "RPOCircuit:699" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> (evalB (precedence id_s `gt` precedence id_t)
                                                                   <|>
                                                              (evalB (precedence id_s `eq` precedence id_t) <&>
                                                               exgt s t)))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     case af_s of
       Left  i  -> safeAtL "RPOCircuit:709" tt_s (pred i) > t
       Right ii -> anyM (>~ t) (sel 5 ii tt_s)

   | otherwise = return False

  exgt, exeq :: Term (TermF id) var -> Term (TermF id) var -> Flip EvalF v Bool
  exgt s t
   | Just id_t <- rootSymbol t, tt <- directSubterms t
   , Just id_s <- rootSymbol s, ss <- directSubterms s = do
        af_s <- compFiltering id_s
        af_t <- compFiltering id_t
        let ss' = applyFiltering af_s ss
            tt' = applyFiltering af_t tt
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True,  True)  -> mulD ss' tt'
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexD (maybe ss' (permute ss) ps)
                 (maybe tt' (permute tt) pt)
          _ -> error "exgt: Cannot compare two symbols with incompatible statuses"

  exeq s t
   | Just id_t <- rootSymbol t, tt <- directSubterms t
   , Just id_s <- rootSymbol s, ss <- directSubterms s = do
        af_s <- compFiltering id_s
        af_t <- compFiltering id_t
        let ss' = applyFiltering af_s ss
            tt' = applyFiltering af_t tt
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True,  True)  -> muleqD ss' tt'
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexeqD (maybe ss' (permute ss) ps)
                   (maybe tt' (permute tt) pt)
          _ -> error "exeq:Cannot compare two symbols with incompatible statuses"

  lexD []     _      = return False
  lexD _      []     = return True
  lexD (f:ff) (g:gg) = (f > g) <|> (f ~~ g <&> lexD ff gg)

  lexeqD []     []     = return True
  lexeqD _      []     = return False
  lexeqD []     _      = return False
  lexeqD (f:ff) (g:gg) = (f ~~ g <&> lexeqD ff gg)

  mulD m1 m2 = do
    m1' <- differenceByM (~~) m1 m2
    m2' <- differenceByM (~~) m2 m1
    forall m2' $ \y-> exists m1' (> y)

  muleqD [] []     = return True
  muleqD (m:m1) m2 = acmatchM (~~m) m2 >>= \it -> case it of
                                                   Just (_,m2) -> muleqD m1 m2
                                                   _           -> return False
  muleqD _ _       = return False

  differenceByM p = foldM rem1 where
    rem1 []     _ = return []
    rem1 (x:xx) y = p x y >>= \b -> if b then return xx else rem1 xx y

  acmatchM p = go [] where
    go acc [] = return Nothing
    go acc (x:xs) = p x >>= \b -> if b then return $ Just (x, reverse acc ++ xs)
                                       else go (x:acc) xs

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
--  evalPerm :: HasStatus id v => id -> Flip Eval v (Maybe [Int])
  evalPerm id = do
    bits <- (T.mapM . mapM . mapM) evalB (lexPerm id)
    let perm = (fmap.fmap)
                 (\perm_i -> head ([i | (i,True) <- zip [1..] perm_i] ++ [-1]))
                 bits
    return perm

  compFiltering id = do
    isList:filtering <- mapM (evalB.input) (listAF_v id : filtering_vv id)
    let positions = [ i | (i, True) <- zip [1..] filtering ]
    return $ if isList then Right positions
             else CE.assert (length positions == 1) $ Left (head positions)

  applyFiltering (Right ii) tt = selectSafe "RPOCircuit.verifyRPOAF.applyFiltering" (map pred ii) tt
  applyFiltering (Left j)   tt = [safeAtL   "RPOCircuit.verifyRPOAF.applyFiltering" tt (pred j)]

  sel6 = sel 6
  sel7 = sel 7
  sel8 = sel 8
  sel9 = sel 9

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
                | NNat v
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
    nat x  = Graph $ do {n <- newNode; return (n, [(n, NNat x)],[])}

instance OneCircuit Graph where
    one tt = Graph$ do
      (tips, nodes, edges) <- unzip3 `liftM` mapM unGraph tt
      me <- newNode
      let nodes' = (me, NOne) : concat nodes
          edges' = [(n, me, EVoid) | n <- tips ] ++ concat edges
      return (me, nodes', edges')

instance Pretty id => RPOCircuit Graph id var where
    termGt t u = Graph $ do
                   n <- newNode
                   let me = (n, NTermGt (show$ pPrint t) (show$ pPrint u))
                   return (n, [me], [])
    termEq t u = Graph $ do
                   n <- newNode
                   let me = (n, NTermEq (show$ pPrint t) (show$ pPrint u))
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
shareGraph :: (G.DynGraph gr, Eq v, Hashable v, Show v, Eq id, Pretty id, Hashable id, Eq tvar, Hashable tvar) =>
              FrozenShared id tvar v -> gr (FrozenShared id tvar v) (FrozenShared id tvar v)
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
    go c@(CExist i) = return (i, [(i, frz c)], [])

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, frz ccode) : (rNode, i, frz ccode) : lEdges ++ rEdges)
    tupM2 f (x, y) = liftM2 (,) (f x) (f y)
    frz ccode = FrozenShared ccode cmaps
    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case Bimap.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x


shareGraph' :: (G.DynGraph gr, Ord v, Hashable v, Show v, Pretty id, Ord id) =>
              FrozenShared id tvar v -> gr String String
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
    go c@(CExist i) = return (i, [(i, frz c)], [])
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
    frz (CVar i) = show $ fromJust $ Bimap.lookup i (varMap cmaps)
    frz CFalse{} = "false"
    frz CTrue{}  = "true"
    frz CNot{}   = "not"
    frz CAnd{} = "/\\"
    frz COr{}  = "\\/"
    frz CIff{} = "<->"
    frz COnlyif{} = "->"
    frz CXor{} = "xor"
    frz CIte{} = "if-then-else"
    frz (CNat c) = "n" ++ show c
    frz CEq{} = "=="
    frz CLt{} = "<"
    frz COne{} = "ONE"
    frz (CExist i) = "v" ++ show i ++ "?"

    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case Bimap.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x

removeExist :: (Hashable id, Ord id, Ord v, Hashable v, Show v, ECircuit c, NatCircuit c, OneCircuit c) => FrozenShared id tvar v -> c v
removeExist (FrozenShared code maps) = go code
  where
  -- dumb (for playing): remove existentials by replacing them with their assigned value (if any)
  existAssigs = Map.fromList $
                [ (f, val)| (f@CExist{}, val) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (val, f@CExist{}) <- Bimap.elems(iffMap maps)]

  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren' c (varMap maps)
  go c@CExist{} = go $ Map.findWithDefault (error "removeExist: CExist") c existAssigs
  go c@(COr{})  = uncurry or  (go `onTup` getChildren c (orMap  maps))
  go c@(CAnd{}) = uncurry and (go `onTup` getChildren c (andMap maps))
  go c@(CNot{}) = not . go $ getChildren c (notMap maps)
  go c@(COne{}) = one . map go $ getChildren c (oneMap maps)
  go c@(CXor{}) = uncurry xor (go `onTup` getChildren c (xorMap  maps))
  go c@(COnlyif{}) = uncurry onlyif (go `onTup` getChildren c (onlyifMap  maps))
  go c@(CIff{}) = uncurry iff (go `onTup` getChildren c (iffMap  maps))
  go c@(CIte{}) = let
      (cc, tc, ec) = getChildren c (iteMap maps)
      [cond, t, e] = map go [cc, tc, ec]
      in ite cond t e

  go c@CNat{} = nat $ getChildren' c (natMap maps)
  go c@CEq{}  = uncurry eq (go `onTup` getChildren c (eqMap  maps))
  go c@CLt{}  = uncurry lt (go `onTup` getChildren c (ltMap  maps))

  onTup f (x, y) = (f x, f y)

-- | Returns an equivalent circuit with no iff, xor, onlyif, ite, nat, eq and lt nodes.
removeComplex :: (Hashable id, Ord id, Ord tvar, Hashable tvar, Ord v, Hashable v, Show v, Circuit c) => [v] -> FrozenShared id tvar v -> (c v, v :->: [v])
removeComplex freshVars c = assert disjoint $ (go code, bitnats)
  where
  -- casting removes the one constraints
  FrozenShared code maps = runShared (castCircuit c) `asTypeOf` c

  -- encoding nats as binary numbers
  bitwidth = fst . head . dropWhile ( (< Bimap.size (natMap maps)) . snd) . zip [1..] . iterate (*2) $ 2
  bitnats  = HashMap.fromList (Bimap.elems (natMap maps) `zip` chunks bitwidth freshVars)
  disjoint = all (`notElem` Bimap.elems (varMap maps))  (concat $ HashMap.elems bitnats)
  lookupBits c = fromJust $ HashMap.lookup (getChildren' c (natMap maps)) bitnats

  -- dumb (for playing): remove existentials by replacing them with their assigned value (if any)
  existAssigs = Map.fromList $
                [ (f, val)| (f@CExist{}, val) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (val, f@CExist{}) <- Bimap.elems(iffMap maps)]

  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren' c (varMap maps)
  go c@CExist{} = go $ Map.findWithDefault (error "removeComplex: CExist") c existAssigs
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
      | (a@CNat{}, b@CNat{}) <- getChildren c (eqMap maps)
      , na <- lookupBits a
      , nb <- lookupBits b
      = eq na nb

      | otherwise
      = typeError "removeComplex: expected a boolean."

  go c@(CLt{})
      | (a@CNat{}, b@CNat{}) <- getChildren c (ltMap maps)
      , na <- lookupBits a
      , nb <- lookupBits b
      = lt na nb

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
  eq [] qq = not $ orL $ map input qq
  eq pp [] = not $ orL $ map input pp

  lt (p:pp) (q:qq) = lt pp qq `or` (not (input p) `and` input q `and` eq pp qq)
  lt [] [] = false
  lt [] qq = orL $ map input qq
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
                    , toBitMap  :: !(CCode :->: [Var])
--                    , toBitMap  :: !(Var :<->: (CCode,Int))
                    , numCnfClauses :: !Int
                    }

emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , numCnfClauses = 0
                    , toCnfMap = Bimap.empty
                    , toBitMap = mempty}

-- retrieve and create (if necessary) a cnf variable for the given ccode.
--findVar :: (MonadState CNFState m) => CCode -> m Lit
findVar ccode = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    return . lit $ v
      Just v'  -> return . lit $ v'

findVar' ccode kfound knot = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    knot $ lit v
      Just v'  -> kfound $ lit v'


recordVar ccode comp = do
    m <- gets toCnfMap
    case Bimap.lookupR ccode m of
      Nothing -> do l <- comp
                    modify $ \s -> s{ toCnfMap = Bimap.insert (var l) ccode (toCnfMap s) }
                    return l
      Just v  -> return (lit v)

-- | A circuit problem packages up the CNF corresponding to a given
-- `FrozenShared' circuit, and the mapping between the variables in the CNF and
-- the circuit elements of the circuit.

data RPOCircuitProblem id tvar v = RPOCircuitProblem
    { rpoProblemCnf     :: CNF
    , rpoProblemCircuit :: !(FrozenShared id tvar v)
    , rpoProblemCodeMap :: !(Var :<->: CCode)
    , rpoProblemBitMap  :: !(Var :->: (CCode,Int)) }

-- Optimal CNF conversion
toCNF' :: (Hashable id, Ord id, Hashable tvar, Ord tvar, Ord v, Hashable v, Show v) => [v] -> FrozenShared id tvar v -> (ECircuitProblem v, v :->: [v])
toCNF' freshv = first(ECircuit.toCNF . ECircuit.runShared) . removeComplex freshv

-- Fast CNF conversion
toCNF :: (Hashable id, Ord id, Ord v, Hashable v, Show v, Hashable tvar, Show tvar, Show id) =>
         FrozenShared id tvar v -> RPOCircuitProblem id tvar v
toCNF c@(FrozenShared !sharedCircuit !circuitMaps) =
    let (m,cnf) = (\x -> execRWS x circuitMaps emptyCNFState) $ do
                     l <- toCNF' sharedCircuit
                     writeClauses [[l]]

        bitMap = HashMap.fromList [ (v, (c,i)) | (c,vv) <- HashMap.toList (toBitMap m), (v,i) <- zip vv [0..]]

    in RPOCircuitProblem
       { rpoProblemCnf = CNF { numVars    = pred $ unVar $ head (toCnfVars m)
                             , numClauses = numCnfClauses m
                             , clauses    = cnf }
       , rpoProblemCircuit = c
       , rpoProblemCodeMap = toCnfMap m
       , rpoProblemBitMap  = bitMap}
  where
    debug msg = hPutStrLn stderr ("toCNFRpo - " ++ msg) >> hFlush stderr

    writeClauses cc = incC (length cc) >> tell cc

    bitWidth  = fst . head
              . dropWhile ( (< Bimap.size (natMap circuitMaps)) . snd )
              . zip [1..] . iterate (*2)
              $ 2

    -- Returns l where {l} U the accumulated c is CNF equisatisfiable with the input
    -- circuit.  Note that CNF conversion only has cases for And, Or, Not, True,
    -- False, and Var circuits.  We therefore remove the complex circuit before
    -- passing stuff to this function.
    toCNF' c@(CVar{})   = findVar' c goOn goOn
    toCNF' c@CExist{}   = findVar' c goOn goOn

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
        m <- ask
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
        m <- asks f
        case Bimap.lookup code m of
          Nothing -> error $ "toCNFRpo: unknown code: " ++ show code
          Just x  -> return x

    findNat c@CNat{} = do
        bm <- gets toBitMap
        case HashMap.lookup c bm of
          Nothing -> do
              bits <- replicateM bitWidth fresh
              modify $ \s -> s{ toBitMap  = HashMap.insert c (map var bits) bm }
              return bits
          Just vv -> return (map lit vv)

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
  projectLits lits = Map.map Right vm `mappend`
                     Map.map (Left . fromBinary . map snd . sortBy (compare `on` fst)) bm
    where
    (vm, bm) =
      foldl (\m l -> case litHash l of
                       Var h   -> insertVar h l m
                       Bit h_i -> insertNat h_i l m
                       Auxiliar-> m)
            (initiallyAllFalseMap, initiallyAllZeroMap)
            (litAssignment lits)

    initiallyAllFalseMap = Map.fromList [(v,False) | v <- Bimap.elems (varMap maps)]
    initiallyAllZeroMap  = Map.empty -- 8fromList [(v,0)     | v <- Bimap.elems (natMap maps)]

    insertVar h l (mb,mn) = (mb',mn) where
         mb' = case Bimap.lookup h (varMap maps) of
                             Nothing -> mb
                             Just v  -> Map.insert v (litSign l) mb

    insertNat (h,i) l (mb,mn) = (mb,mn') where
         mn' = case Bimap.lookup h (natMap maps) of
                          Nothing -> mn
                          Just n  -> Map.insertWith (++) n [(i, litSign l)] mn

    litHash l = case Bimap.lookup (var l) codeMap of
                  Nothing -> case HashMap.lookup (var l) bitsMap of
                               Just (code,bit) -> Bit (circuitHash code, bit)
                               Nothing    -> Auxiliar
                  Just code -> Var (circuitHash code)

    safeAt l i = CE.assert (i < length l) (l !! i)
data ProjectionCase = Var CircuitHash | Bit (CircuitHash, Int) | Auxiliar



-- ------------------------
-- Hashable instances
-- ------------------------
{-
instance Hashable Var where
  newtype Var :->: x = VarTrie (Int :->: x)
  empty = VarTrie HashMap.empty
  lookup (V i) (VarTrie t) = HashMap.lookup i t
  insert (V i) v (VarTrie t) = VarTrie (HashMap.insert i v t)
  toList (VarTrie t) = map (first V) (HashMap.toList t)
-}
instance Hashable Var where hash (V i) = i
-- -------
-- Errors
-- -------

typeError :: String -> a
typeError msg = error (msg ++ "\nPlease send an email to the pepeiborra@gmail.com requesting a typed circuit language.")


