{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Narradar.Constraints.SAT.Z3Circuit
   ( solve
   ) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Concurrent
import Control.DeepSeq
import Control.Monad.List
import Control.Monad.State (StateT(..), runStateT, MonadState(..), gets, modify)
import Control.Monad.Trans (MonadIO(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Foldable (Foldable, foldMap, toList)
import Data.List( nub, foldl', sortBy, (\\))
import Data.Map.Strict( Map )
import Data.Maybe( fromJust, catMaybes )
import Data.Hashable
--import Data.NarradarTrie (HasTrie, (:->:) )
import Data.Monoid (Monoid(..))
import Data.Set( Set )
import Data.Traversable (Traversable, traverse)
import System.IO
import Prelude hiding( not, and, or, (>) )

import Narradar.Constraints.RPO (Status(..))
import Narradar.Constraints.SAT.RPOAF.Symbols
import Narradar.Constraints.SAT.MonadSAT        hiding (and,or)
import Narradar.Utils (debug, debug', on, firstM)
import Narradar.Framework (TimeoutException(..))
import Narradar.Framework.Ppr
import Narradar.Types.Term
import Narradar.Types.Problem.NarrowingGen

import qualified Control.Exception as CE (assert, throw, catch, evaluate)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
--import qualified Data.NarradarTrie as Trie
import qualified Funsat.Circuit  as Circuit
import qualified Funsat.ECircuit as ECircuit
import qualified Funsat.TermCircuit as TermCircuit
import qualified Narradar.Types.Var as Narradar
import qualified Prelude as Prelude
import qualified Data.HashMap as Trie
import qualified Data.Term.Family as Family

import Funsat.ECircuit ( Circuit(..)
                       , ECircuit(..)
                       , CastCircuit(..)
                       , NatCircuit(..)
                       , ExistCircuit(..)
                       , BIEnv
                       )

import Funsat.TermCircuit( TermCircuit(..)
                         , AssertCircuit(..)
                         , OneCircuit(..)
                         , HasStatus(..)
                         , HasPrecedence(..)
                         , HasFiltering(..)
                         , IsSimple(..)
                         , oneExist
                         , runEvalM)

import Funsat.TermCircuit.Ext (TermExtCircuit(..))
import Funsat.TermCircuit.RPO as RPO

import Funsat.TermCircuit.Symbols (Natural(..))

import System.TimeIt

import Z3.Monad
import Narradar.Utils ((<$$>))

newtype Z3Source id var = Z3Source { unZ3Source :: StateT (Z3State id var) Z3 AST }

data VarType = Bool | Nat deriving (Eq, Ord, Show)

data Z3State id var = Z3State
  { termMaps  :: !(VarMaps AST id var)
  , variables :: !(Map (var,VarType) AST)
  , boolSort  :: Maybe Sort
  , intSort   :: Maybe Sort
  , exist_pool:: !Int
  }

recordVariable v val me@Z3State{variables} = me{variables = Map.insert v val variables}

emptyState = Z3State mempty mempty Nothing Nothing 0

updateGtMap f it@Z3State{termMaps} = it{ termMaps = termMaps{ termGtMap = f (termGtMap termMaps)}}
updateEqMap f it@Z3State{termMaps} = it{ termMaps = termMaps{ termEqMap = f (termEqMap termMaps)}}

type instance Family.Id   (Z3Source id) = id
type instance Family.Var  (Z3Source id) = Narradar.Var
type instance Family.TermF(Z3Source id) = TermF id

instance Circuit (Z3Source id) where
  type Co (Z3Source id) var = (Ord var, Show var)

  true  = lift0 mkTrue
  false = lift0 mkFalse
  not   = lift1 mkNot
  andL [] = true
  andL xx = liftL mkAnd xx
  orL  [] = false
  orL  xx = liftL mkOr  xx
  and a b = andL [a,b]
  or  a b = orL  [a,b]
  input v = Z3Source$ do
    vars <- gets variables
    case Map.lookup (v,Bool) vars of
     Just v -> return v
     Nothing -> do
       sym  <- mkStringSymbol (show v)
       sort <- getBoolSort
       me <- mkConst sym sort
       modify $ recordVariable (v,Bool) me
       return me

instance ECircuit (Z3Source id) where
  iff  = lift2 mkEq
  ite  = lift3 mkIte

instance CastCircuit (Z3Source id) (Z3Source id) where
  type CastCo (Z3Source id) (Z3Source id) v = ()
  castCircuit = id

instance NatCircuit (Z3Source id) where
  nat v = Z3Source $ do
    vars <- gets variables
    case Map.lookup (v,Nat) vars of
     Just v -> return v
     Nothing -> do
       sym  <- mkStringSymbol (show v)
       sort <- getIntSort
       me <- mkConst sym sort
       modify $ recordVariable (v,Nat) me
       return me

  gt = lift2 mkGt
  eq = lift2 mkEq
  lt = lift2 mkLt

instance OneCircuit (Z3Source id)

instance ExistCircuit(Z3Source id) where
  existsBool f = Z3Source $ do
    n <- gets exist_pool
    modify $ \z -> z{exist_pool = n+1}
    sort <- getBoolSort
    sym  <- mkStringSymbol ("exist" ++ show n)
    me <- mkConst sym sort
    unZ3Source $ f $ Z3Source $ return me

instance AssertCircuit (Z3Source id) where
  assertCircuit assC c = Z3Source $ do
    ass <- unZ3Source assC
    assertCnstr ass
    unZ3Source c

instance (Hashable id, Pretty id, Ord id, IsSimple id, TermExtCircuit (Z3Source id) id
         ) =>
    TermCircuit (Z3Source id) where
 type CoTerm_ (Z3Source id) (TermF id) tv v = (tv ~ Narradar.Var)

 termGt s t = Z3Source $ do
      env <- gets (termGtMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> mdo
           modify $ updateGtMap $ Trie.insert (s,t) me
           me <- unZ3Source $ RPO.termGt_ s t
           return me

 termEq s t = Z3Source $ do
      env <- gets (termEqMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> mdo
           modify $ updateEqMap $ Trie.insert (s,t) me
           me   <- unZ3Source $ RPO.termEq_ s t
           return me

-- -----------------------
-- MonadSAT implementation
-- -----------------------

data Z3S id v = Z3S
  { stZ  :: !(Z3State id v)
  , pool :: [v]
  }

newtype Z3M id v a = Z3M {unZ3M :: StateT (Z3S id v) Z3 a} deriving (Functor, Monad, MonadIO)

runZ3Source (Z3Source z) = Z3M $ do
  st <- gets stZ
  (res, st') <- lift $ runStateT z st
  modify $ \z -> z{stZ = st'}
  return res

instance (Hashable v, Ord v, Show v) => MonadSAT (Z3Source id) v (Z3M id v) where
  boolean_ _ = do
    s@Z3S{pool = h:t} <- Z3M (gets id)
    Z3M $ put s{pool = t}
    return h
  natural_ l = Natural <$> boolean_ l
  assert_ _ aa = do
    a <- runZ3Source (orL aa)
    Z3M $ assertCnstr a

solve :: (Enum v, Ord v, Show v, Hashable v, NFData v
         ,Ord id, Show id, Pretty id, Hashable id
         ) => v -> Z3M id v (EvalM v a) -> IO (Maybe a)
solve start (Z3M m) = evalZ3 $ do
  (me, Z3S{stZ=Z3State{variables}}) <- runStateT m (Z3S emptyState [start ..])
  liftM (join.snd) $ withModel $ \model -> runMaybeT $ do
      vv   <- MaybeT $ evalT model (toList variables)
      env_ <- zipWithM ((MaybeT.) . readVar) (Map.keys variables) vv
      env  <- liftIO $ CE.evaluate $ force env_
      return (runEvalM (Map.fromList env) me)

readVar (k,Bool) v = ((k,) . Right) <$$> getBool v
readVar (k,Nat)  v = (Just . (k,) . Left . fromInteger) <$> getInt v

-- --------
-- Helpers
-- --------

lift0 = Z3Source
lift1 f a = Z3Source $ do
  va <- unZ3Source a
  lift $ f va
lift2 f a b = Z3Source $ do
  va <- unZ3Source a
  vb <- unZ3Source b
  lift $ f va vb
lift3 f a b c = Z3Source $ do
  va <- unZ3Source a
  vb <- unZ3Source b
  vc <- unZ3Source c
  lift $ f va vb vc
liftL f xx = Z3Source $ do
  vv <- sequence (map unZ3Source xx)
  lift $ f vv

getBoolSort = do
  bs <- gets boolSort
  case bs of
   Just bs' -> return bs'
   Nothing -> do
     bs' <- mkBoolSort
     modify $ \st -> st{boolSort = Just bs'}
     return bs'

getIntSort = do
  bs <- gets intSort
  case bs of
   Just bs' -> return bs'
   Nothing -> do
     bs' <- mkIntSort
     modify $ \st -> st{intSort = Just bs'}
     return bs'

-- Missing instances

instance MonadZ3 m => MonadZ3 (StateT s m) where
  getSolver  = lift getSolver
  getContext = lift getContext
