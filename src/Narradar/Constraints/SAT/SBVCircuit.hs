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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Narradar.Constraints.SAT.SBVCircuit
   ( solveRPO, solveWPO
   , RPOM, WPOM
   ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad.List
import Control.Monad.Reader (MonadReader(..), ReaderT(..), runReaderT)
import Control.Monad.State (StateT(..), runStateT, MonadState(..), gets, modify)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Foldable (toList)
import Data.Map.Strict( Map )
import Data.Maybe (fromMaybe, catMaybes)
import Data.Hashable
import Data.Monoid (Monoid(..))
import Data.IORef
import System.IO
import Prelude hiding( not, and, or, (>) )

import Narradar.Constraints.SAT.RPOAF (EnvRPO(..))
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

import Funsat.ECircuit as Funsat
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

import qualified Data.SBV as SBV
import Data.SBV
import Unsafe.Coerce
import Debug.Hoed.Observe
import Prelude ()
import qualified Prelude

data SSBV = forall a . SSBV (SBV a)

instance Observable (SBV a) where observer = observeBase
instance Observable1 SBV where observer1 = observeBase
instance Observable SSBV where observer  (SSBV x) p = SSBV(observer x p)

newtype SBVSource id var = SBVSource { unSBVSource :: StateT (SBVState id var) Symbolic SSBV }

instance Observable v => Observable (SBVSource id v) where
  observer fn ctxt = SBVSource $ do
    res <- unSBVSource fn
    return (observer res ctxt)

data BoolOrNat b n = Bool b | Nat n deriving (Eq, Ord, Show)

data SBVState id var = SBVState
  { termMaps  :: !(VarMaps SSBV id var)
  , variables :: !(Map (BoolOrNat var var) SSBV)
  , w0        :: Maybe (Natural var)
  }

recordVariable v val me@SBVState{variables} = me{variables = Map.insert v val variables}

emptyState = SBVState mempty mempty Nothing

updateGtMap f it@SBVState{termMaps} = it{ termMaps = termMaps{ termGtMap = f (termGtMap termMaps)}}
updateGeMap f it@SBVState{termMaps} = it{ termMaps = termMaps{ termGeMap = f (termGeMap termMaps)}}
updateEqMap f it@SBVState{termMaps} = it{ termMaps = termMaps{ termEqMap = f (termEqMap termMaps)}}

type instance Family.Id   (SBVSource id) = id
type instance Family.Var  (SBVSource id v) = v
type instance Family.TermF(SBVSource id) = TermF id

type instance Co (SBVSource id) var = (Ord var, Show var)
instance Circuit (SBVSource id) where

  true  = lift0 (SBV.true :: SBool)
  false = lift0 (SBV.false :: SBool)
  not   = lift1 (bnot :: SBool -> SBool)
  andL [] = Funsat.true
  andL xx = liftL (bAnd :: [SBool] -> SBool) xx
  orL  [] = Funsat.false
  orL [a] = a
  orL[a,b] = or a b
  orL  xx = liftL (bOr :: [SBool] -> SBool)  xx
  and     = lift2 ((&&&) :: SBool -> SBool -> SBool)
  or      = lift2 ((|||) :: SBool -> SBool -> SBool)
  input v = SBVSource$ do
    vars <- gets variables
    case Map.lookup (Bool v) vars of
     Just v -> return v
     Nothing -> do
       me <- lift $ sBool (show v)
       modify $ recordVariable (Bool v) (SSBV me)
       return (SSBV me)

instance ECircuit (SBVSource id) where
  iff  = lift2 ( (<=>) :: SBool -> SBool -> SBool)
  ite  = lift3 ( SBV.ite :: SBool -> SBool -> SBool -> SBool)

instance CastCircuit (SBVSource id) (SBVSource id) where
  type CastCo (SBVSource id) (SBVSource id) v = ()
  castCircuit = id

type SInt = SInteger

instance NatCircuit (SBVSource id) where
  nat (Natural v) = SBVSource $ do
    vars <- gets variables
    case Map.lookup (Nat v) vars of
     Just v -> return v
     Nothing -> do
       me <- lift $ sInteger (show v)
       modify $ recordVariable (Nat v) (SSBV me)
       return (SSBV me)

  gt = lift2 (.>)
  eq = lift2 (.==)
  lt = lift2 (.<)

  (+#) = lift2 addSInt
  (-#) = lift2 subSInt
  (*#) = lift2 mulSInt

  fromInteger = lift0 . mkSInt

  iteNat  = lift3 ( SBV.ite :: SBool -> SInt -> SInt -> SInt)

instance MaxCircuit (SBVSource id) where
  max = lift2 maxSInt

addSInt, subSInt, mulSInt :: SInteger -> SInteger -> SInteger
addSInt = (+)
subSInt = (-)
mulSInt = (*)

maxSInt :: SInteger -> SInteger -> SInteger
maxSInt = smax

mkSInt :: Integer -> SInteger
mkSInt = fromIntegral

instance OneCircuit (SBVSource id)

instance ExistCircuit(SBVSource id) where
  existsBool f = SBVSource $ do
    me :: SBool <- lift exists_
    unSBVSource $ f $ SBVSource $ return (SSBV me)

instance AssertCircuit (SBVSource id) where
  assertCircuit assC c = SBVSource $ do
    SSBV ass <- unSBVSource assC
    lift $ constrain (unsafeCoerce ass)
    unSBVSource c

-- ----
-- RPO
-- ----
newtype RPOCircuit id v = RPOCircuit { unRPO :: SBVSource id v } deriving Observable

type instance Family.Id    (RPOCircuit id) = id
type instance Family.TermF (RPOCircuit id) = TermF id
type instance Family.Var   (RPOCircuit id var) = var

type instance Co (RPOCircuit id) v = Co (SBVSource id) v
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

 termGt s t = RPOCircuit $ SBVSource $ do
      env <- gets (termGtMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> do
           me <- unSBVSource $ unRPO $ RPO.termGt_ s t
           modify $ updateGtMap $ Trie.insert (s,t) me
           return me

 termEq s t = RPOCircuit $ SBVSource $ do
      env <- gets (termEqMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> do
           me   <- unSBVSource $ unRPO $ RPO.termEq_ s t
           modify $ updateEqMap $ Trie.insert (s,t) me
           return me

-- ----
-- WPO
-- ----
newtype WPOCircuit id v = WPOCircuit { unWPO :: SBVSource id v } deriving Observable

type instance Family.Id    (WPOCircuit id) = id
type instance Family.TermF (WPOCircuit id) = TermF id
type instance Family.Var   (WPOCircuit id var) = var

type instance Co (WPOCircuit id) v = Co (SBVSource id) v
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

 termGt s t = WPOCircuit $ SBVSource $ do
      env <- gets (termGtMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v -> return v
         Nothing -> do
           me <- unSBVSource $ unWPO $ WPO.termGt_ s t
           modify $ updateGtMap $ Trie.insert (s,t) me
           return me

 termGe s t = WPOCircuit $ SBVSource $ do
      env <- gets (termGeMap.termMaps)
      case Trie.lookup (s,t) env of
         Just v  -> return v
         Nothing -> do
           me   <- unSBVSource $ unWPO $ WPO.termGe_ s t
           modify $ updateGeMap $ Trie.insert (s,t) me
           return me

instance (WPO.WPOAlgebra (WPOCircuit id)
         ) => WPO.WPOCircuit (WPOCircuit id) where
  w0 = WPOCircuit $ SBVSource $ do
       v <- gets w0
       unSBVSource $ unWPO $ nat (fromMaybe (error "w0") v)

instance ( WPO.WPOAlgebra (WPOCircuit id)
         , HasFiltering id, HasPrecedence id, HasStatus id, Eq id
          ) => TermExtCircuit (WPOCircuit id) id where
  exGt = lexpgt
  exEq = lexpeq

-- -----------------------
-- MonadSAT implementation
-- -----------------------

data SBVS id v = SBVS
  { stZ  :: !(SBVState id v)
  , pool :: !([v])
  , constraints :: !([SBool])
  , ob   :: Observer
  }

emptySBVS start ob = SBVS emptyState [start..] [] ob

newtype SBVM (repr :: * -> * -> *) id v a = SBVM {unSBVM :: StateT (SBVS id v) Symbolic a} deriving (Applicative, Functor, Monad)

newtype RPOM id v a = RPOM { unRPOM :: SBVM RPOCircuit id v a } deriving (Applicative, Functor, Monad)
instance MonadReader (EnvRPO (RPOCircuit id) v) (RPOM id v) where ask = return EnvRPO

newtype WPOM id v a = WPOM {unWPOM :: ReaderT (EnvWPO (WPOCircuit id) v) (SBVM WPOCircuit id v) a}
                    deriving (Functor, Applicative, Monad, MonadReader (EnvWPO (WPOCircuit id) v))

class    SBVCircuit repr       where run :: repr id v -> SBVM repr id v SSBV
instance SBVCircuit RPOCircuit where run  = runSBVSource . unRPO
instance SBVCircuit WPOCircuit where run  = runSBVSource . unWPO

runSBVSource :: SBVSource id v -> SBVM repr id v SSBV
runSBVSource (SBVSource z) = SBVM $ do
  st <- gets stZ
  (res, st') <- lift $ runStateT z st
  modify $ \z -> z{stZ = st'}
  return res

instance (Hashable v, Ord v, Show v, Taggable v, Observable v
         ,Observable (repr id v)
         ,Co (repr id) v, OneCircuit (repr id), ECircuit (repr id), NatCircuit (repr id), MaxCircuit (repr id)
         ,SBVCircuit repr
         ) => MonadSAT (repr id) v (SBVM repr id v) where
  boolean_ name = do
    s@SBVS{pool = h:t} <- SBVM (gets id)
    SBVM $ put s{pool = t}
    return (tagWith name h)
  natural_ l = Natural <$> boolean_ l
  assert_ _ [] = return ()
  assert_ label [a] = do
    a <- run a
    SBVM $ modify $ \st -> st{constraints = unpack a : constraints st}
    return ()
  assert_ label [a,b] = do
    a <- run (or a b)
    SBVM $ modify $ \st -> st{constraints = unpack a : constraints st}
    return ()
  assert_ label aa = do
    a <- run (orL aa)
    SBVM $ modify $ \st -> st{constraints = unpack a : constraints st}
    return ()

deriving instance (Hashable v, Ord v, Show v, Taggable v, Observable v
                   ) =>  MonadSAT (RPOCircuit id) v (RPOM id v)

instance (Hashable v, Ord v, Show v, Taggable v, Observable v
         ) => MonadSAT (WPOCircuit id) v (WPOM id v) where
  boolean_ i   = WPOM $ lift $ boolean_ i
  natural_ i   = WPOM $ lift $ natural_ i
  assert_  i x = WPOM $ lift $ assert_  i x

solve_ msg ob@(O o _) start opts (SBVM m) = do
  putStr ("Starting SBV up for " ++ show msg ++ " ...")
  meRef   <- newIORef Nothing
  varsRef <- newIORef Nothing
  let query = do
      (me, SBVS{stZ=SBVState{variables}, constraints}) <- runStateT m (emptySBVS start ob)
      liftIO $ writeIORef meRef   (Just me)
      liftIO $ writeIORef varsRef (Just variables)
      forAll_ (bAnd $ o "constraints" constraints)
  (solver,satResult) <- satWithAny opts query
#ifdef DEBUG
  smt <- compileToSMTLib SMTLib2  True query
  _ <- CE.evaluate $ force $ o "smt" smt
#endif
  Just variables <- readIORef varsRef
  Just me        <- readIORef meRef
  let success = modelExists satResult
--  _ <- CE.evaluate $ force $ o "satResult" $ show satResult
  putStrLn (if success then "yes" else "no")
  return$ if Prelude.not success then Nothing else
    let env  = Map.fromList $ o "env" $ catMaybes $ [ readVar v satResult | v <- Map.keys variables ]
    in Just $ runEvalM env me

solveRPO :: (Enum v, Ord v, Show v, Hashable v, NFData v, Observable v
            ,Ord id, Show id, Pretty id, Hashable id
            ,Observable a, Show msg
            ) => msg -> Observer -> v -> [SMTConfig] -> RPOM id v (EvalM v a) -> IO (Maybe a)
solveRPO msg obs start opts (RPOM circuit) = solve_ msg obs start opts $ circuit

-- | Initialize the WPO environment and call solve
solveWPO ::
  (Enum v, Ord v, Ord t, Show v, Hashable v, Observable v, Taggable v, Show msg) =>
  msg
  -> Observer
  -> v
  -> [SMTConfig]
  -> WPOM t v (EvalM v a)
  -> IO (Maybe a)
solveWPO msg obs start opts (WPOM circuit) = solve_ msg obs start opts $ do
  w0 <- natural_ "w0"
  SBVM $ modify $ \st -> st{stZ = (stZ st){w0 = Just w0}}
  runReaderT circuit (EnvWPO w0)

readVar (Bool k) m = ((k,) . Right) <$> getModelValue (show k) m
readVar (Nat k)  m = ((k,) . Left . cast ) <$> getModelValue (show k) m
  where cast :: Integer -> Int
        cast = fromIntegral

instance Observable SatResult where observer = observeBase
instance Observable SMTConfig where observer = observeBase

instance Observable1 (RPOM id v) where
  observer1 fn cxt =
        do c <- RPOM $ SBVM $ gets constraints
           res <- fn
           c' <- RPOM $ SBVM $ gets constraints
           let msg = "<RPOM " ++ show c ++ " ==> " ++ show c' ++ ">"
           send msg (return return << res) cxt

instance Observable1 (WPOM id v) where
  observer1 fn cxt =
        do res <- fn
           send "<WPOM>" (return return << res) cxt

instance Observable a => Observable (WPOM id v a) where
  observers = observers1
  observer = observer1
instance Observable a => Observable (RPOM id v a) where
  observers = observers1
  observer = observer1


-- --------
-- Helpers
-- --------

unpack :: SSBV -> SBV a
unpack (SSBV x) = unsafeCoerce x

-- lift2Nat = lift2 (

lift0 :: (SBV a) -> SBVSource id var
lift0 = SBVSource . return .  SSBV
lift1 :: (SBV a -> SBV b) -> SBVSource id var -> SBVSource id var
lift1 f a = SBVSource $ do
  va <- unSBVSource a
  return $ SSBV $ f (unpack va)
lift2 :: (SBV a -> SBV a -> SBV a) -> SBVSource id var -> SBVSource id var -> SBVSource id var
lift2 f a b = SBVSource $ do
  va <- unSBVSource a
  vb <- unSBVSource b
  return $ SSBV $ f (unpack va) (unpack vb)
lift3 f a b c = SBVSource $ do
  va <- unSBVSource a
  vb <- unSBVSource b
  vc <- unSBVSource c
  return $ SSBV $ f (unpack va) (unpack vb) (unpack vc)
liftL f xx = SBVSource $ do
  vv <- sequence (map unSBVSource xx)
  return $ SSBV $ f (map unpack vv)
{-# INLINE lift0 #-}
{-# INLINE lift1 #-}
{-# INLINE lift2 #-}
{-# INLINE lift3 #-}
{-# INLINE liftL #-}
