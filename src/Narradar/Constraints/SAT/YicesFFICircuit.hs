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
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Narradar.Constraints.SAT.YicesFFICircuit
   (Circuit(..)
   ,ECircuit(..)
   ,NatCircuit(..)
   ,OneCircuit(..)
   ,RPOCircuit(..)
   ,RPOExtCircuit(..)
   ,ExistCircuit(..)
   ,YicesSource(..), YMaps(..)
   ,solveYicesSource, runYicesSource, runYicesSource', emptyYMaps
   ,computeBIEnv
   ) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Concurrent
import Control.DeepSeq
import Control.Monad.List
import Control.Monad.Reader
import Control.Monad.State hiding ((>=>), forM_)
import Data.Foldable (Foldable, foldMap)
import Data.List( nub, foldl', sortBy, (\\))
import Data.Bimap( Bimap )
import Data.Map( Map )
import Data.Maybe( fromJust, catMaybes )
import Data.NarradarTrie (HasTrie, (:->:) )
import Data.Monoid
import Data.Set( Set )
import Data.Traversable (Traversable, traverse)
import Bindings.Yices
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

import Narradar.Constraints.SAT.RPOCircuit ( RPOCircuit(..), RPOExtCircuit(..), OneCircuit(..), oneExist)

newtype YicesSource id var = YicesSource { unYicesSource :: StateT (YMaps id var) IO Expr}

data VarType = Bool | Nat deriving (Eq, Ord, Show)


data YMaps id var = YMaps
    { context   :: Context
    , variables :: !(Bimap (var, VarType) Expr)
    , termGtMap :: !((TermN id, TermN id) :->: Expr)
    , termGeMap :: !((TermN id, TermN id) :->: Expr)
    , termEqMap :: !((TermN id, TermN id) :->: Expr)
    }
  deriving Show

emptyYMaps ctx = YMaps ctx Bimap.empty mempty mempty mempty

fromDefWithDefault _ (YDef val) = val
fromDefWithDefault def _ = def

solveYicesSource :: (HasTrie id, Ord var, Show var) =>
              YicesSource id var -> IO (Maybe(BIEnv var))

solveYicesSource m = do {yst <- runYicesSource m; computeBIEnv yst <* delContext (context yst)}

computeBIEnv :: (Ord var, Show var) => YMaps id var -> IO (Maybe(BIEnv var))
computeBIEnv YMaps{variables,context=ctx} = do

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

runYicesSource (YicesSource y) = do
  ctx                        <- mkContext
  declareGenAndGoal ctx
  (constraint, ym@YMaps{..}) <- runStateT y (emptyYMaps ctx)
  assert ctx constraint
  return ym
   where
    declareGenAndGoal = return

runYicesSource' stY (YicesSource y) = runStateT y stY

instance Circuit (YicesSource id) where
  true  = liftY0 mkTrue
  false = liftY0 mkFalse

  input v = YicesSource $ do
              vars <- gets variables
              case Bimap.lookup (v, Bool) vars of
               Just v  -> return v
               Nothing -> do
                  ctx <- gets context
                  me <- lift $ mkBoolVar ctx (show v)
                  modify $ \y -> y{variables = Bimap.insert (v,Bool) me (variables y)}
                  return me

  not x = liftY1 mkNot x
  and   = liftY2 mkAnd2
  or    = liftY2 mkOr2
  andL [] = liftY0 mkTrue
  andL xx = YicesSource $ do
              vv  <- sequence (map unYicesSource xx)
              ctx <- gets context
              lift (mkAnd ctx vv)

  orL []  = liftY0 mkFalse
  orL xx = YicesSource $ do
              vv  <- sequence (map unYicesSource xx)
              ctx <- gets context
              lift (mkOr ctx vv)

instance ECircuit (YicesSource id) where
  iff  = liftY2 mkEq
  ite  = liftY3 mkIte

instance NatCircuit (YicesSource id) where

  nat v = YicesSource $ do
              vars <- gets variables
              ctx  <- gets context
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
          ctx   <- gets context
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
      ctx <- gets context
      v   <- liftIO $ mkFreshBoolVar ctx
      unYicesSource $ f (YicesSource $ return v)

instance (HasTrie id, Pretty id, Ord id, RPOExtCircuit (YicesSource id) id Narradar.Var) =>
    RPOCircuit (YicesSource id) id Narradar.Var where
 termGt s t = YicesSource $ do
      env <- gets termGtMap
      ctx <- gets context
--      liftIO $ debug (show $ text "Looking up" <+> s <+> text ">" <+> t)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> do
--           liftIO $ debug (show $ text "Constructing" <+> s <+> text ">" <+> t)
           me_v <- liftIO $ mkFreshBoolVar ctx
           modify $ \env -> env{termGtMap = Trie.insert (s,t) me_v (termGtMap env)}
           me <- unYicesSource $ RPOCircuit.termGt_ s t
--           liftIO $ debug (show $ text "Declaring" <+> s <+> text ">" <+> t)
           liftIO $ assert ctx =<< mkEq ctx me_v me
           return me_v
 termEq s t = YicesSource $ do
      env <- gets termEqMap
      ctx <- gets context
--      liftIO $ debug (show $ text "Looking up" <+> s <+> text "~" <+> t)
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> do
--           liftIO $ debug (show $ text "Constructing" <+> s <+> text "~" <+> t)
           me_v <- lift $ mkFreshBoolVar ctx
           modify $ \env -> env{termEqMap = Trie.insert (s,t) me_v (termEqMap env)}
           me   <- unYicesSource $ RPOCircuit.termEq_ s t
--           liftIO $ debug (show $ text "Declaring" <+> s <+> text "~" <+> t)
           liftIO $ assert ctx =<< mkEq ctx me_v me
           return me_v
{-
 termGe s t = YicesSource $ do
      env <- gets termGeMap
      ctx <- gets context
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

liftY0 f   = YicesSource (gets context >>= lift.f)
liftY1 f a = YicesSource $ do
  va <- unYicesSource a
  ctx <- gets context
  lift $ f ctx va
liftY2 f a b = YicesSource $ do
  va <- unYicesSource a
  vb <- unYicesSource b
  ctx <- gets context
  lift  $ f ctx va vb
liftY3 f a b c = YicesSource $ do
  va <- unYicesSource a
  vb <- unYicesSource b
  vc <- unYicesSource c
  ctx <- gets context
  lift $ f ctx va vb vc
