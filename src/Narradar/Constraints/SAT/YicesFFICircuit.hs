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
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Narradar.Constraints.SAT.YicesFFICircuit
   (Circuit(..)
   ,ECircuit(..)
   ,NatCircuit(..)
   ,OneCircuit(..)
   ,RPOCircuit(..)
   ,RPOExtCircuit(..)
   ,ExistCircuit(..)
   ,AssertCircuit(..)
   ,YicesSource(..), YMaps(..)
   ,emptyYMaps
   ,runYicesSource
   ,computeBIEnv
   ) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Concurrent
import Control.DeepSeq
import Control.Monad.List
import Control.Monad.RWS hiding ((>=>), forM_)
import Control.Monad.Writer (runWriter)
import Data.Foldable (Foldable, foldMap)
import Data.List( nub, foldl', sortBy, (\\))
import Data.Bimap( Bimap )
import Data.Map( Map )
import Data.Maybe( fromJust, catMaybes )
import Data.NarradarTrie (HasTrie, (:->:) )
import Data.Monoid
import Data.Set( Set )
import Data.Traversable (Traversable, traverse)
import Bindings.Yices as Yices
import System.IO
import Prelude hiding( not, and, or, (>) )

import Narradar.Constraints.RPO (Status(..))
import Narradar.Constraints.SAT.RPOAF.Symbols
import Narradar.Utils (debug, on, firstM)
import Narradar.Framework (TimeoutException(..))
import Narradar.Framework.Ppr
import Narradar.Types.Term
import Narradar.Types.Problem.NarrowingGen

import qualified Control.Exception as CE (assert, throw, catch, evaluate)
import qualified Data.Bimap as Bimap
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.NarradarTrie as Trie
import qualified Funsat.Circuit  as Circuit
import qualified Funsat.ECircuit as ECircuit
import qualified Narradar.Constraints.SAT.RPOCircuit as RPOCircuit
import qualified Narradar.Types.Var as Narradar
import qualified Prelude as Prelude

import Funsat.ECircuit ( Circuit(..)
                       , ECircuit(..)
                       , NatCircuit(..)
                       , ExistCircuit(..)
                       , BIEnv)

import Narradar.Constraints.SAT.RPOCircuit ( RPOCircuit(..)
                                           , RPOExtCircuit(..)
                                           , AssertCircuit(..)
                                           , OneCircuit(..)
                                           , oneExist)

newtype YicesSource id var = YicesSource { unYicesSource :: RWST Context () (YMaps id var) IO Expr}

data VarType = Bool | Nat deriving (Eq, Ord, Show)

data YMaps id var = YMaps
    { variables :: !(Bimap (var, VarType) Expr)
    , termGtMap :: !((TermN id, TermN id) :->: Expr)
    , termGeMap :: !((TermN id, TermN id) :->: Expr)
    , termEqMap :: !((TermN id, TermN id) :->: Expr)
    }
  deriving Show

emptyYMaps = YMaps Bimap.empty mempty mempty mempty

runYicesSource  ctx stY (YicesSource y) = do
  (a, stY',()) <- runRWST y ctx stY
  return (a,stY')

fromDefWithDefault _ (YDef val) = val
fromDefWithDefault def _ = def

computeBIEnv :: (Ord var, Show var) => Context -> YMaps id var -> IO (Maybe(BIEnv var))
computeBIEnv ctx YMaps{variables} = do

  res <- newEmptyMVar

  sat <- do tid <- forkIO $ putMVar res =<< maxSat ctx
            takeMVar res
          `CE.catch` \TimeoutException -> do
            debug "timeout: interrupting Yices"
            interrupt ctx -- on interrupt, Yices ends immediately returning 'unsat'
            takeMVar res
            CE.throw TimeoutException

  case sat of
    YDef True  -> do
      model <- getModel' ctx
      result<- runListT $ do
                    (v, typ) <- msum $ map return $ Bimap.keys variables
                    Just vd  <- lift $ getVarDecl ctx (show v)
                    lift$ case typ of
                      Bool -> do
                               val <- fromDefWithDefault False <$> getBoolValue model vd
                               return (v, Right val)
                      Nat  -> do
                               val <- fromDefWithDefault 0 <$> getNatValue model vd
                               return (v, Left val)

      CE.evaluate (map snd result `deepseq` ())
      return $ Just $ Map.fromList result

    _ -> return Nothing

instance Circuit (YicesSource id) where
  true  = liftY0 mkTrue
  false = liftY0 mkFalse

  input v = YicesSource $ do
              vars <- gets variables
              case Bimap.lookup (v, Bool) vars of
               Just v  -> return v
               Nothing -> do
                  ctx <- ask
                  me <- lift $ mkBoolVar ctx (show v)
                  modify $ \y -> y{variables = Bimap.insert (v,Bool) me (variables y)}
                  return me

  not x = liftY1 mkNot x
  and   = liftY2 mkAnd2
  or    = liftY2 mkOr2
  andL [] = liftY0 mkTrue
  andL xx = YicesSource $ do
              vv  <- sequence (map unYicesSource xx)
              ctx <- ask
              lift (mkAnd ctx vv)

  orL []  = liftY0 mkFalse
  orL xx = YicesSource $ do
              vv  <- sequence (map unYicesSource xx)
              ctx <- ask
              lift (mkOr ctx vv)

instance ECircuit (YicesSource id) where
  iff  = liftY2 mkEq
  ite  = liftY3 mkIte

instance NatCircuit (YicesSource id) where

  nat v = YicesSource $ do
              vars <- gets variables
              ctx  <- ask
              case (v, Nat) `Bimap.lookup` vars of
                Just v  -> return v
                Nothing -> do
                  me <- lift $ mkNatVar ctx (show v)
                  modify $ \y -> y{variables = Bimap.insert (v,Nat) me (variables y)}
                  return me

  gt = liftY2 mkGt
  eq = liftY2 mkEq
  lt = liftY2 mkLt

instance OneCircuit (YicesSource id) where
--  one = oneExist
{-
  one [] = false
  one vv = YicesSource $ do
          ctx   <- ask
          ones_vv  <- lift $ replicateM (length vv) (mkFreshBoolVar ctx)
          zeros_vv <- lift $ replicateM (length vv) (mkFreshBoolVar ctx)
          let ones  = map (YicesSource . return) ones_vv
              zeros = map (YicesSource . return) zeros_vv
          mapM_ ( (lift . assert ctx =<<) . unYicesSource) $
                  concat
                  [ [ one_i  `iff` ite b_i zero_i1 one_i1
                    , zero_i `iff` (not b_i `and` zero_i1)]
                   | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                      zip5 vv ones zeros (tail ones ++ [false]) (tail zeros ++ [true])
                  ]
          return (head ones_vv)
      where
       zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee)
           = (a,b,c,d,e) : zip5 aa bb cc dd ee
       zip5 _ _ _ _ _ = []
-}

instance ExistCircuit (YicesSource id) where
  exists f = YicesSource $ do
      ctx <- ask
      v   <- liftIO $ mkFreshBoolVar ctx
      unYicesSource $ f (YicesSource $ return v)

instance AssertCircuit (YicesSource id) where
  assertCircuit assC c = YicesSource $ do
      ctx <- ask
      ass <- unYicesSource assC
      liftIO $ Yices.assert ctx ass
      unYicesSource c

instance (HasTrie id, Pretty id, Ord id, RPOExtCircuit (YicesSource id) id Narradar.Var) =>
    RPOCircuit (YicesSource id) id Narradar.Var where
 termGt s t = YicesSource $ do
      env <- gets termGtMap
      ctx <- ask
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> mdo
           modify $ \env -> env{termGtMap = Trie.insert (s,t) me (termGtMap env)}
           me <- unYicesSource $ RPOCircuit.termGt_ s t
           return me

 termEq s t = YicesSource $ do
      env <- gets termEqMap
      ctx <- ask
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> mdo
           modify $ \env -> env{termEqMap = Trie.insert (s,t) me (termEqMap env)}
           me   <- unYicesSource $ RPOCircuit.termEq_ s t
           return me

{-
 termGe s t = YicesSource $ do
      env <- gets termGeMap
      ctx <- ask
--      liftIO $ debug (show $ text "Looking up" <+> s <+> text ">" <+> t)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> do
--           liftIO $ debug (show $ text "Constructing" <+> s <+> text ">" <+> t)
           me_v <- liftIO $ mkFreshBoolVar ctx
           modify $ \env -> env{termGeMap = Trie.insert (s,t) me_v (termGeMap env)}
           me <- unYicesSource $ RPOCircuit.termGe_ s t
--           liftIO $ debug (show $ text "Declaring" <+> s <+> text ">" <+> t)
           liftIO $ assert ctx =<< mkEq ctx me_v me
           return me_v
-}
{-# INLINE liftY0 #-}
{-# INLINE liftY1 #-}
{-# INLINE liftY2 #-}
{-# INLINE liftY3 #-}

liftY0 f   = YicesSource (ask >>= lift.f)
liftY1 f a = YicesSource $ do
  va <- unYicesSource a
  ctx <- ask
  lift $ f ctx va
liftY2 f a b = YicesSource $ do
  va <- unYicesSource a
  vb <- unYicesSource b
  ctx <- ask
  lift  $ f ctx va vb
liftY3 f a b c = YicesSource $ do
  va <- unYicesSource a
  vb <- unYicesSource b
  vc <- unYicesSource c
  ctx <- ask
  lift $ f ctx va vb vc
