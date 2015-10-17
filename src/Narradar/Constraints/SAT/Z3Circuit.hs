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
   ( solveRPO, solveWPO, Z3MRPO, Z3MWPO
   ) where

import Control.Applicative
import Control.DeepSeq
import qualified Control.Exception as CE
import Control.Monad.List
import Control.Monad.Reader (MonadReader(..), ReaderT(..), runReaderT)
import Control.Monad.State.Strict (StateT(..), runStateT, MonadState(..), gets, modify)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Foldable (toList)
import Data.Map.Strict( Map )
import Data.Maybe (fromMaybe)
import Data.Hashable
--import Data.NarradarTrie (HasTrie, (:->:) )
import Data.Maybe
import Data.Monoid (Monoid(..))
import System.IO
import Prelude hiding( not, and, or, (>) )

import Lens.Family.State.Strict

import Narradar.Constraints.SAT.RPOAF (EnvRPO)
import Narradar.Constraints.SAT.WPO   (EnvWPO(..))
import Narradar.Constraints.SAT.MonadSAT        hiding (and,or)
import Narradar.Framework.Ppr
import Narradar.Types.Term

import qualified Control.Exception as CE (evaluate)
import qualified Data.Map.Strict as Map
--import qualified Data.NarradarTrie as Trie
import qualified Narradar.Types.Var as Narradar
import qualified Data.HashMap as Trie
import qualified Data.Term.Family as Family

import Funsat.ECircuit  as Funsat
                       ( Circuit(..), Co
                       , ECircuit(..)
                       , CastCircuit(..)
                       , NatCircuit(..), Natural(..)
                       , MaxCircuit(..)
                       )

import Funsat.TermCircuit( TermCircuit(..), CoTerm_
                         , runEvalM)

import Funsat.TermCircuit.Ext(
                           TermExtCircuit(..),
                           lexpgt, lexpeq
                         )

import qualified Funsat.TermCircuit.RPO as RPO
import qualified Funsat.TermCircuit.WPO as WPO


import Z3.Monad
import Narradar.Utils ((<$$>))

import Debug.Hoed.Observe (Observer(..))
import Data.Maybe (fromJust)

import Debug.Hoed.Observe

newtype Z3Source id var = Z3Source { unZ3Source :: StateT (Z3State id var) Z3 AST }

data VarType = Bool | Nat deriving (Eq, Ord, Show)

data Z3State id var = Z3State
  { termMaps  :: !(VarMaps AST id var)
  , variables :: !(Map (var,VarType) AST)
  , _boolSort  :: Maybe Sort
  , _intSort   :: Maybe Sort
  , exist_pool:: !Int
  , _w0        :: Maybe (Natural var)
  }
instance Observable AST where observer = observeOpaque "AST"
instance Observable v => Observable (Z3Source id v) where
  observer fn ctxt = Z3Source $ do
    res <- unZ3Source fn
    return (observer res ctxt)

w0       f it@Z3State{_w0}       = fmap (\x -> it{_w0=x})       (f _w0)
boolSort f it@Z3State{_boolSort} = fmap (\x -> it{_boolSort=x}) (f _boolSort)
intSort  f it@Z3State{_intSort}  = fmap (\x -> it{_intSort=x})  (f _intSort)

recordVariable v val me@Z3State{variables} = me{variables = Map.insert v val variables}

emptyState = Z3State mempty mempty Nothing Nothing 0 Nothing

updateGtMap f it@Z3State{termMaps} = it{ termMaps = termMaps{ termGtMap = f (termGtMap termMaps)}}
updateGeMap f it@Z3State{termMaps} = it{ termMaps = termMaps{ termGeMap = f (termGeMap termMaps)}}
updateEqMap f it@Z3State{termMaps} = it{ termMaps = termMaps{ termEqMap = f (termEqMap termMaps)}}

type instance Family.Id   (Z3Source id) = id
type instance Family.Var  (Z3Source id var) = var
type instance Family.TermF(Z3Source id) = TermF id

type instance Co (Z3Source id) var = (Ord var, Show var)
instance Circuit (Z3Source id) where
  true  = lift0 mkTrue
  false = lift0 mkFalse
  not   = lift1 mkNot
  andL [] = true
  andL[x] = x
  andL[x,y]= and x y
  andL xx = liftL mkAnd xx
  and     = lift2 (\x y -> mkAnd [x,y])
  orL  [] = false
  orL [x] = x
  orL[x,y]= or x y
  orL  xx = liftL mkOr  xx
  or      = lift2 (\x y -> mkOr [x,y])
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
  nat (Natural v) = Z3Source $ do
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
  x +# y = liftL mkAdd [x,y]
  x -# y = liftL mkSub [x,y]
  x *# y = liftL mkMul [x,y]
  fromInteger i = lift0 (mkInteger i)

  iteNat = lift3 mkIte

instance OneCircuit (Z3Source id)

instance MaxCircuit (Z3Source id) where
  -- TODO is there a more efficient implementation ?
  max x y = iteNat (gt x y) x y

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
    solverAssertCnstr ass
    unZ3Source c

-- type instance CoTerm_ (Z3Source id) (TermF id) tv v = (tv ~ Narradar.Var)

-- ----
-- RPO
-- ----
newtype RPOCircuit id v = RPOCircuit { unRPO :: Z3Source id v } deriving Observable

type instance Family.Id    (RPOCircuit id) = id
type instance Family.TermF (RPOCircuit id) = TermF id
type instance Family.Var   (RPOCircuit id var) = var

type instance Co (RPOCircuit id) v = Co (Z3Source id) v
deriving instance Circuit       (RPOCircuit id)
deriving instance ECircuit      (RPOCircuit id)
deriving instance NatCircuit    (RPOCircuit id)
deriving instance AssertCircuit (RPOCircuit id)
deriving instance ExistCircuit  (RPOCircuit id)
deriving instance OneCircuit    (RPOCircuit id)
deriving instance MaxCircuit    (RPOCircuit id)

type instance CoTerm_ (RPOCircuit id) (TermF id) tv v = (tv ~ Narradar.Var)

instance ( Hashable id, Pretty id, Ord id
         , IsSimple id, HasFiltering id, HasPrecedence id, HasStatus id, HasLexMul id
         , TermExtCircuit (RPOCircuit id) id
         ) =>
    TermCircuit (RPOCircuit id) where

 termGt s t = RPOCircuit $ Z3Source $ do
      env <- gets (termGtMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> mdo
           modify $ updateGtMap $ Trie.insert (s,t) me
           me <- unZ3Source $ unRPO $ RPO.termGt_ s t
           return me

 termEq s t = RPOCircuit $ Z3Source $ do
      env <- gets (termEqMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> mdo
           modify $ updateEqMap $ Trie.insert (s,t) me
           me   <- unZ3Source $ unRPO $ RPO.termEq_ s t
           return me

-- ----
-- WPO
-- ----
newtype WPOCircuit id v = WPOCircuit { unWPO :: Z3Source id v } deriving Observable

type instance Family.Id    (WPOCircuit id) = id
type instance Family.TermF (WPOCircuit id) = TermF id
type instance Family.Var   (WPOCircuit id var) = var

type instance Co (WPOCircuit id) v = Co (Z3Source id) v
deriving instance Circuit       (WPOCircuit id)
deriving instance ECircuit      (WPOCircuit id)
deriving instance NatCircuit    (WPOCircuit id)
deriving instance AssertCircuit (WPOCircuit id)
deriving instance ExistCircuit  (WPOCircuit id)
deriving instance OneCircuit    (WPOCircuit id)
deriving instance MaxCircuit    (WPOCircuit id)

type instance CoTerm_ (WPOCircuit id) (TermF id) tv v = (tv ~ Narradar.Var)

instance ( Hashable id, Pretty id, Ord id
         , WPO.WPOAlgebra (WPOCircuit id)
         , TermExtCircuit (WPOCircuit id) id
         , WPO.WPOSymbol id
         ) =>
    TermCircuit (WPOCircuit id) where

 termGt s t = WPOCircuit $ Z3Source $ do
      env <- gets (termGtMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> mdo
           modify $ updateGtMap $ Trie.insert (s,t) me
           me <- unZ3Source $ unWPO $ WPO.termGt_ s t
           return me

 termGe s t = WPOCircuit $ Z3Source $ do
      env <- gets (termGeMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> mdo
           modify $ updateGeMap $ Trie.insert (s,t) me
           me   <- unZ3Source $ unWPO $ WPO.termGe_ s t
           return me

instance (WPO.WPOAlgebra (WPOCircuit id)
         ) => WPO.WPOCircuit (WPOCircuit id) where
  w0 = WPOCircuit $ Z3Source $ do
       v <- use w0
       unZ3Source $ unWPO $ nat (fromMaybe (error "w0") v)

instance ( WPO.WPOAlgebra (WPOCircuit id)
         , HasFiltering id, HasPrecedence id, HasStatus id, Eq id
          ) => TermExtCircuit (WPOCircuit id) id where
  exGt = lexpgt
  exEq = lexpeq

-- -----------------------
-- MonadSAT implementation
-- -----------------------

class Z3Circuit repr where
  run :: repr id v -> Z3M repr id v AST

data Z3S id v = Z3S
  { _stZ  :: !(Z3State id v)
  , _pool :: ![v]
  }

stZ  f (Z3S _stZ _pool) = fmap (\x' -> Z3S x' _pool) (f _stZ)
pool f (Z3S _stZ _pool) = fmap (\x' -> Z3S _stZ x' ) (f _pool)

newtype Z3M (m :: * -> * -> *) id v a =
  Z3M {unZ3M :: StateT (Z3S id v) Z3 a} deriving (Functor, Applicative, Monad, MonadIO)

type Z3MRPO = Z3M RPOCircuit
instance MonadReader (EnvRPO (RPOCircuit id) v) (Z3MRPO id v) where
  ask = error "unimplementable (EnvRPO has no constructors)"
  local = error "unimplementable (EnvRPO has no constructors)"

newtype Z3MWPO id v a = Z3MWPO {unWPOCircuit :: ReaderT (EnvWPO (WPOCircuit id) v) (Z3M WPOCircuit id v) a}
                    deriving (Functor, Applicative, Monad, MonadIO, MonadReader (EnvWPO (WPOCircuit id) v))

runZ3Source (Z3Source z) = Z3M $ do
  st <- use stZ
  (res, st') <- lift $ runStateT z st
  stZ .= st'
  return res

instance Z3Circuit RPOCircuit where run = runZ3Source . unRPO
instance Z3Circuit WPOCircuit where run = runZ3Source . unWPO

instance (Hashable v, Ord v, Show v, Z3Circuit repr
         ,Co (repr id) v, OneCircuit (repr id), ECircuit (repr id), NatCircuit (repr id), MaxCircuit (repr id)
         ) => MonadSAT (repr id) v (Z3M repr id v) where
  boolean_ _ = Z3M $ do
    h:t <- use pool
    pool .= t
    return h
  natural_ l = Natural <$> boolean_ l
  assert_ _ [] = return ()
  assert_ _ aa = do
    ast <- run (orL aa)
    Z3M$ solverAssertCnstr ast

instance (Hashable v, Ord v, Show v) => MonadSAT (WPOCircuit id) v (Z3MWPO id v) where
  boolean_ i   = Z3MWPO $ lift $ boolean_ i
  natural_ i   = Z3MWPO $ lift $ natural_ i
  assert_  i x = Z3MWPO $ lift $ assert_  i x

solve :: (Enum v, Ord v, Show v, Hashable v, NFData v
         ,Ord id, Show id, Pretty id, Hashable id
         ,Z3Circuit m, Show msg
         ) => msg -> Observer -> v -> Z3M m id v (EvalM v a) -> Z3 (Maybe a)
solve msg (O o oo) start (Z3M m) = do
  (me, Z3S{_stZ=Z3State{variables}}) <- runStateT m (Z3S emptyState [start ..])
  liftIO $ putStr ("solving " ++ show msg ++ " with Z3...")
  (res, a) <- withModel $ \model -> runMaybeT $ do
      vv   <- MaybeT $ evalT model (toList variables)
      env_ <- zipWithM ((MaybeT.) . readVar) (Map.keys variables) vv
      env  <- liftIO $ CE.evaluate $ force env_
      return (runEvalM (Map.fromList env) me)
  _ <- liftIO $ CE.evaluate $ force $ o "res" $ show res
  liftIO $ print res
  return (join a)

solveRPO :: (Enum v, Ord v, Show v, Hashable v, NFData v
         ,Ord id, Show id, Pretty id, Hashable id
         ,Show msg
         ) => msg -> Observer -> v -> Z3MRPO id v (EvalM v a) -> IO (Maybe a)
solveRPO msg obs start z3 = evalZ3 $ solve msg obs start z3
solveWPO :: (Enum v, Ord v, Show v, Hashable v, NFData v
         ,Ord id, Show id, Pretty id, Hashable id
         ,Show msg
         ) => msg -> Observer -> v -> Z3MWPO id v (EvalM v a) -> IO (Maybe a)
solveWPO msg obs start z3 =
  evalZ3 $ solve msg obs start $ do
    w0v <- natural_ "w0"
    Z3M (stZ.w0 .= Just w0v)
    runReaderT (unWPOCircuit z3) (EnvWPO w0v)


readVar (k,Bool) v = ((k,) . Right) <$$> getBoolValue v
readVar (k,Nat)  v = (Just . (k,) . Left . Prelude.fromInteger) <$> getInt v


instance Observable1 (Z3M repr id v) where
  observer1 fn cxt =
        do res <- fn
           send "<Z3M>" (return return << res) cxt

instance Observable a => Observable (Z3M repr id v a) where
  observers = observers1
  observer = observer1

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
  bs <- use boolSort
  case bs of
   Just bs' -> return bs'
   Nothing -> do
     boolSort <~ Just <$> mkBoolSort
     fromJust <$> use boolSort

getIntSort = do
  bs <- use intSort
  case bs of
   Just bs' -> return bs'
   Nothing -> do
     intSort <~ Just <$> mkIntSort
     fromJust <$> use intSort

-- Missing instances

instance MonadZ3 m => MonadZ3 (StateT s m) where
  getSolver  = lift getSolver
  getContext = lift getContext
