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

module Narradar.Constraints.SAT.YicesFFICircuit
   (solve
   ) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Concurrent
import Control.DeepSeq
import Control.Monad.List
import Control.Monad.RWS (RWST, runRWST, MonadReader(..), MonadState(..), gets, modify)
import Control.Monad.Writer (runWriter)
import Data.Foldable (Foldable, foldMap)
import Data.List( nub, foldl', sortBy, (\\))
import           Data.Bimap                               (Bimap)
import qualified Data.Bimap                               as Bimap
import Data.Map( Map )
import Data.Maybe( fromJust, catMaybes )
import Data.Hashable
--import Data.NarradarTrie (HasTrie, (:->:) )
import Data.Monoid (Monoid(..))
import Data.Set( Set )
import Data.Traversable (Traversable, traverse)
import Bindings.Yices as Yices
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
import qualified Data.Bimap as Bimap
import qualified Data.Map as Map
import qualified Data.Set as Set
--import qualified Data.NarradarTrie as Trie
import qualified Funsat.Circuit  as Circuit
import qualified Funsat.ECircuit as ECircuit
import qualified Funsat.TermCircuit as RPOCircuit
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
                         , oneExist
                         , runEvalM)
import Funsat.TermCircuit.Ext ( TermExtCircuit(..) )
import Funsat.TermCircuit.Symbols (Natural(..))
import Funsat.TermCircuit.RPO as RPO

import System.TimeIt

type YMaps = VarMaps Expr

data VarType = Bool | Nat deriving (Eq, Ord, Show)

data YState id var = YState
  { varmaps   :: VarMaps Expr id var
  , variables :: !(Bimap (var, VarType) Expr)
  }

emptyYState = YState mempty Bimap.empty

updateGtMap f it@YState{varmaps} = it{ varmaps = varmaps{ termGtMap = f (termGtMap varmaps)}}
updateEqMap f it@YState{varmaps} = it{ varmaps = varmaps{ termEqMap = f (termEqMap varmaps)}}

newtype YicesSource id var = YicesSource { unYicesSource :: RWST Context () (YState id var) IO Expr}

type instance Family.Id    (YicesSource id) = id
type instance Family.TermF (YicesSource id) = TermF id
type instance Family.Var   (YicesSource id) = Narradar.Var

runYicesSource ctx stY (YicesSource y) = do
  (a, stY',()) <- runRWST y ctx stY
  return (a,stY')

fromDefWithDefault _ (YDef val) = val
fromDefWithDefault def _ = def

computeBIEnv :: (Ord var, Show var) => Context -> YState id var -> IO (Maybe(BIEnv var))
computeBIEnv ctx YState{variables} = do

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
  type Co (YicesSource id) var = (Ord var, Show var)
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

instance CastCircuit (YicesSource id) (YicesSource id) where
  type CastCo (YicesSource id) (YicesSource id) v = ()
  castCircuit = id

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
  existsBool f = YicesSource $ do
      ctx <- ask
      v   <- liftIO $ mkFreshBoolVar ctx
      unYicesSource $ f (YicesSource $ return v)
{-
  existsNat f = YicesSource $ do
      ctx <- ask
      v   <- liftIO $ mkFreshNatVar ctx
      unYicesSource $ f (YicesSource $ return v)
-}
instance AssertCircuit (YicesSource id) where
  assertCircuit assC c = YicesSource $ do
      ctx <- ask
      ass <- unYicesSource assC
      liftIO $ Yices.assert ctx ass
      unYicesSource c

instance (Hashable id, Pretty id, Ord id, TermExtCircuit (YicesSource id) id
         ,RPOCircuit.IsSimple id
         ) =>
    TermCircuit (YicesSource id) where
 type CoTerm_ (YicesSource id) (TermF id) tv v = (tv ~ Narradar.Var)

 termGt s t = YicesSource $ do
      env <- gets (termGtMap.varmaps)
      ctx <- ask
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> mdo
           modify $ updateGtMap $ Trie.insert (s,t) me
           me <- unYicesSource $ RPO.termGt_ s t
           return me

 termEq s t = YicesSource $ do
      env <- gets (termEqMap.varmaps)
      ctx <- ask
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> mdo
           modify $ updateEqMap $ Trie.insert (s,t) me
           me   <- unYicesSource $ RPO.termEq_ s t
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

-- ----------------------------
-- MonadSAT implementation
-- ----------------------------

data StY' id v = StY' { poolY' :: ![v]
                      , stY'   :: !(YState id v)
                      }

newtype SMTY' id v a = SMTY' {unSMTY' :: RWST Context () (StY' id v) IO a}
    deriving (Functor, Monad, MonadIO, MonadReader Context, MonadState (StY' id v))

solve :: (Enum v, Ord v, Show v, Hashable v
          ,Hashable id, Ord id, Show id, Pretty id
          ) => SMTY' id v (EvalM v a) -> IO (Maybe a)
solve = solve' 1
solve' start (SMTY' my) = do
  ctx <- mkContext
#ifdef DEBUG
--  setVerbosity 10
  setLogFile "yices.log"
#endif
  (me, StY'{stY'}, _) <- runRWST my ctx (StY' [toEnum start ..] emptyYState)
--  let symbols = getAllSymbols $ mconcat
--                [ Set.fromList [t, u] | ((t,u),_) <- HashMap.toList (termGtMap stY) ++ HashMap.toList (termEqMap stY)]
  debug' "Calling Yices..."
#ifdef DEBUG
#endif
  (ti, bienv) <- timeItT(computeBIEnv ctx stY')
--  debug (unlines $ map show $ Set.toList symbols)
--  debug (show . vcat . map (uncurry printGt.second fst) . HashMap.toList . termGtMap $ stY)
--  debug (show . vcat . map (uncurry printEq.second fst) . HashMap.toList . termEqMap $ stY)
  debug ("done (" ++ show ti ++ " seconds)")
#ifdef DEBUG
--  removeFile "yices.log"
#endif
  delContext ctx
  return $ (`runEvalM` me) <$> bienv

 where
  printEq (t,u) v = v <> colon <+> t <+> text "=" <+> u
  printGt (t,u) v = v <> colon <+> t <+> text ">" <+> u


instance (Enum v, Ord v, Show v, Hashable v) => MonadSAT (YicesSource id) v (SMTY' id v) where
  boolean_ _ = do {st@StY'{poolY' = h:t} <- get; put st{poolY'=t}; return h}
  natural_ _ = do {b <- boolean; return (Natural b)}
  assert_ _ [] = return ()
  assert_ _ a  = do
      st  <- gets stY'
      ctx <- ask
      (me, new_stY) <- liftIO $ runYicesSource ctx st $ orL a
      liftIO $ Yices.assert ctx me
      modify $ \st -> st{stY' = new_stY}
  assertW w a = do
      st  <- gets stY'
      ctx <- ask
      (me, new_stY) <- liftIO $ runYicesSource ctx st $ orL a
      liftIO $ Yices.assertWeighted ctx me w
      modify $ \st -> st{stY' = new_stY}
