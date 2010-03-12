{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Constraints.SAT.Solve
    ( BIEnv, EvalM, runEvalM
    , module Narradar.Constraints.SAT.Solve
    ) where

import Bindings.Yices ( mkContext, interrupt, setVerbosity, assertWeighted
                      , setLogFile, delContext, isInconsistent)
import Control.Applicative
import Control.Arrow (first,second)
import Control.Exception (evaluate, try, SomeException)
import Control.Monad.State
import Data.Array.Unboxed
import Data.List (unfoldr)
import Data.Monoid
import Data.NarradarTrie (HasTrie, (:->:))
import qualified Data.NarradarTrie as Trie
import Data.Term.Rules (getAllSymbols)
import Funsat.Circuit (BEnv, and,or,not)
import Funsat.Types (Clause,Solution(..))
import Math.SMT.Yices.Syntax
import System.Directory
import System.FilePath
import System.IO
import System.IO.Unsafe
import System.Process
import System.TimeIt
import Text.Printf

import Narradar.Constraints.SAT.RPOCircuit hiding (nat)
import Narradar.Constraints.SAT.YicesCircuit as Serial
        (YicesSource, YMaps(..), emptyYMaps, runYices', generateDeclarations, solveDeclarations)
import Narradar.Constraints.SAT.YicesFFICircuit as FFI
        (YicesSource, YMaps(..), runYicesSource', emptyYMaps, computeBIEnv)
import Narradar.Framework (TimeoutException(..))
import Narradar.Framework.Ppr
import Narradar.Utils( debug, readProcessWithExitCodeBS )

import qualified Bindings.Yices as Yices
import qualified Control.Exception as CE
import qualified Funsat.Solver as Funsat
import qualified Funsat.Types as Funsat
import qualified Funsat.ECircuit as ECircuit
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Narradar.Types as Narradar
import qualified Narradar.Constraints.SAT.RPOCircuit as RPOCircuit

import Prelude hiding (and, not, or, any, all, lex, (>))
import qualified Prelude as P

-- --------
-- MonadSAT
-- --------

class (Monad m, Functor m, ECircuit repr, OneCircuit repr, HasTrie v, Ord v, Show v) =>
 MonadSAT repr v m | m -> repr v where
  boolean :: m v
  natural :: m (Natural v)
  assert  :: [repr v] -> m ()
  assertW :: Weight -> [repr v] -> m ()
  assertW _ = assert

newtype Var = V Int deriving (Eq, Ord, Num, Enum)

instance Show Var where show (V i) = "v" ++ show i
instance Read Var where
  readsPrec p ('v':rest) = [(V i, rest) | (i,rest) <- readsPrec 0 rest]
  readsPrec _ _ = []
instance Bounded Var where minBound = V 0; maxBound = V maxBound
instance HasTrie Var where
  newtype Var :->: x = VarTrie (Int :->: x)
  empty = VarTrie Trie.empty
  lookup (V i) (VarTrie t) = Trie.lookup i t
  insert (V i) v (VarTrie t) = VarTrie (Trie.insert i v t)
  toList (VarTrie t) = map (first V) (Trie.toList t)

newtype Natural v = Natural {encodeNatural::v} deriving (Eq,Ord,Show)

lit (V i) = Funsat.L i

instance Pretty Var where pPrint (V i) = text "v" <> i

nat :: (Ord v, HasTrie v, Show v) => NatCircuit repr => Natural v -> repr v
nat (Natural n) = ECircuit.nat n

type Weight = Int

-- ---------------------
-- Interpreting booleans
-- ---------------------
type Precedence = [Integer]

class Decode a b var | a b -> var where decode :: a -> EvalM var b

instance Decode (Eval var) Bool var where decode = evalB
instance Decode (Eval var) Int var  where decode = evalN
instance Decode a b var => Decode [a] [b] var where decode = mapM decode
instance (Decode a a' var, Decode b b' var ) => Decode (a, b) (a',b') var where
  decode (a, b) = do {va <- decode a; vb <- decode b; return (va,vb)}

--instance Decode var Bool var where decode = evalB . input
instance Decode Var Bool Var where decode = evalB . input
instance Decode Var Int Var  where decode = evalN . input
instance (Ord v, HasTrie v, Show v) => Decode (Natural v) Int v where decode = evalN . nat

evalDecode :: (Ord var, HasTrie var, Show var, Decode (Eval var) b var) => Eval var -> EvalM var b
evalDecode x = decode x

-- ----------------------------
-- SMT MonadSAT implementation
-- ----------------------------

-- *** serialized


data StY id = StY { poolY :: [Var]
                  , cmdY  :: [CmdY]
                  , stY   :: Serial.YMaps id Var
                  }

newtype SMTY id a = SMTY {unSMTY :: State (StY id) a} deriving (Functor, Monad, MonadState (StY id))

smtSerial :: (HasTrie id, Ord id, Show id, Pretty id) => Int -> SMTY id (EvalM Var a) -> IO (Maybe a)
smtSerial timeout (SMTY my) = do
  let (me, StY{..}) = runState my (StY [V 2 ..] [] Serial.emptyYMaps)
--  let symbols = getAllSymbols $ mconcat [ Set.fromList [t, u] | ((t,u),_) <- Trie.toList (termGtMap stY) ++ Trie.toList (termEqMap stY)]
  bienv <- solveDeclarations (Just timeout) (generateDeclarations stY ++ cmdY)
--  debug (unlines $ map show $ Set.toList symbols)
--  debug (show . vcat . map (uncurry printGt.second fst) . Trie.toList . termGtMap $ stY)
--  debug (show . vcat . map (uncurry printEq.second fst) . Trie.toList . termEqMap $ stY)
  return ( (`runEvalM` me) <$> bienv )
 where
  printEq (t,u) v = v <> colon <+> t <+> text "=" <+> u
  printGt (t,u) v = v <> colon <+> t <+> text ">" <+> u

instance MonadSAT (Serial.YicesSource id) Var (SMTY id) where
  boolean = do {st <- get; put st{poolY=tail (poolY st)}; return (head $ poolY st)}
  natural = do {b <- boolean; return (Natural b)}
  assert [] = return ()
  assert a  = do
      st <- gets stY
      let (me, stY') = runYices' st $ foldr or false a
      modify $ \st -> st{cmdY = ASSERT me : cmdY st, stY = stY'}
  assertW w a = do
      st <- gets stY
      let (me, st') = runYices' st $ foldr or false a
      modify $ \st -> st{cmdY = ASSERT_P me (Just $ fromIntegral w) : cmdY st, stY = st'}

-- *** FFI

data StY' id = StY' { poolY' :: ![Var]
                    , stY'   :: !(FFI.YMaps id Var)
                    }

newtype SMTY' id a = SMTY' {unSMTY' :: StateT (StY' id) IO a} deriving (Functor, Monad, MonadIO, MonadState (StY' id))

smtFFI :: (HasTrie id, Ord id, Show id, Pretty id) => SMTY' id (EvalM Var a) -> IO (Maybe a)
smtFFI (SMTY' my) = do
  ctx <- mkContext
#ifdef DEBUG
--  setVerbosity 10
--  setLogFile "yices.log"
#endif
  (me, StY'{..}) <- runStateT my (StY' [V 2 ..] (FFI.emptyYMaps ctx))
--  let symbols = getAllSymbols $ mconcat
--                [ Set.fromList [t, u] | ((t,u),_) <- Trie.toList (termGtMap stY) ++ Trie.toList (termEqMap stY)]
#ifdef DEBUG
  debug "Calling Yices..."
#endif
  bienv <- computeBIEnv stY'
            `CE.catch` \TimeoutException -> do
              debug "seen timeout exception"
              CE.throw TimeoutException
--  debug (unlines $ map show $ Set.toList symbols)
--  debug (show . vcat . map (uncurry printGt.second fst) . Trie.toList . termGtMap $ stY)
--  debug (show . vcat . map (uncurry printEq.second fst) . Trie.toList . termEqMap $ stY)
#ifdef DEBUG
  debug "done"
--  removeFile "yices.log"
#endif
  delContext ctx
  return $ (`runEvalM` me) <$> bienv

 where
  printEq (t,u) v = v <> colon <+> t <+> text "=" <+> u
  printGt (t,u) v = v <> colon <+> t <+> text ">" <+> u


instance MonadSAT (FFI.YicesSource id) Var (SMTY' id) where
  boolean = do {st <- get; put st{poolY'=tail (poolY' st)}; return (head $ poolY' st)}
  natural = do {b <- boolean; return (Natural b)}
  assert [] = return ()
  assert a  = do
      st <- gets stY'
      (me, new_stY) <- liftIO $ runYicesSource' st $ orL a
      liftIO $ Yices.assert (context st) me
      modify $ \st -> st{stY' = new_stY}
  assertW w a = do
      st <- gets stY'
      (me, new_stY) <- liftIO $ runYicesSource' st $ orL a
      liftIO $ Yices.assertWeighted (context st) me w
      modify $ \st -> st{stY' = new_stY}

-- ------------------------------------------
-- Boolean Circuits MonadSAT implementation
-- ------------------------------------------
data St tid tvar v = St { pool     :: [v]
                        , circuit  :: !(Shared tid tvar v)
                        , weightedClauses :: [(Weight, Clause)]}

newtype SAT tid tvar v a = SAT {unSAT :: State (St tid tvar v) a} deriving (Functor, Monad, MonadState (St tid tvar v))

instance (Ord v, HasTrie v, Show v) => MonadSAT (Shared tid tvar) v (SAT tid tvar v) where
  boolean = do {st <- get; put st{pool=tail (pool st)}; return (head $ pool st)}
  natural = do {b <- boolean; return (Natural b)}
  assert   [] = return ()
  assert    a = do {st <- get; put st{circuit = orL a `and` circuit st}}
  assertW w a = return () -- = do {st <- get; put st{weightedClauses = ( w, a) : weightedClauses st}}

assertAll :: MonadSAT repr v m => [repr v] -> m ()
assertAll = mapM_ (assert . (:[]))

st0 = St [minBound..] true []


-- *** SAT based (using Yices) solver

data YicesOpts = YicesOpts {maxWeight :: Int, timeout :: Maybe Int}
defaultYicesOpts = YicesOpts 0 Nothing

satYices :: (HasTrie id, Ord id, Show id) => YicesOpts -> SAT id Narradar.Var Var (EvalM Var a) -> IO (Maybe a)
satYices = satYices' [toEnum 1 ..]
satYices' pool0 yo (SAT m) = do
  let (val, St _ circuit weighted) = runState m (St pool0 true [])
  let circuitProb = toCNF(runShared circuit)
  mb_sol <- solveYices yo (rpoProblemCnf circuitProb) weighted val
  return $ fmap (\sol -> runEvalM (projectRPOCircuitSolution sol circuitProb) val) mb_sol

satYicesSimp = satYicesSimp' [toEnum 1 ..]
satYicesSimp' pool0 yo (SAT m) = do
  let (val, St pool circuit weighted) = runState m (St pool0 true [])
      (circuitProb, natbits) = toCNF' pool (runShared circuit)

  mb_sol <- solveYices yo (eproblemCnf circuitProb) weighted val
  return $ do
    sol <- mb_sol
    let bienv = reconstructNatsFromBits (Trie.toList natbits) $ projectECircuitSolution sol circuitProb
    return $ runEvalM bienv val

solveYices YicesOpts{..} cnf weighted val = do
    let nv            = numVars cnf
        nc            = numClauses cnf

    -- feed the problem to Yices
        cs     = map (\c -> unwords (show maxWeight : map show c ++ ["0"] ))
                     (clauses cnf)
        wcs    = map (\(w,c) -> unwords (show w : map show c ++ ["0"]))
                     weighted
        header = printf "p wcnf %d %d %d" nv (nc + length wcs) maxWeight
        opts =  ["-e","-d","-ms", "-mw", show maxWeight] ++ maybe [] (\t -> ["-tm", show t]) timeout


    ( code, the_stdout, the_stderr ) <- readProcessWithExitCode "yices" opts (unlines $ header : wcs ++ cs)

    debug the_stderr

    mb_time <- either (\(e::SomeException) -> "")
                      (\(t::Double) -> "(in " ++ show t ++ " seconds)")
                  <$> (CE.try $ readIO (head $ words the_stderr))

    case lines the_stdout of
        "sat" : xs : _ -> do
            debug ("satisfiable" ++ mb_time)
            return $ Just $ Sat $ array (Funsat.V 0, Funsat.V nv)
                                        [ (Funsat.V(abs x), x) | x <- map read (words xs)]
        _ -> do
            debug ("not satisfiable" ++ mb_time)
            return Nothing

-- *** Funsat solver by simplification to vanilla Circuits

solveFun :: ( HasTrie id, Ord id, Bounded v
            , Enum v, Show v, Ord v
            , HasTrie v, HasTrie tv, Show tv) =>
            SAT id tv v (EvalM v a) -> Maybe a
solveFun = fmap (uncurry $ flip runEvalM) . runFun

solveFunDirect :: ( HasTrie id, Ord id, Show id
                  , Bounded v, Enum v, Ord v, Show v
                  , HasTrie v, HasTrie tv, Show tv) =>
                  SAT id tv v (EvalM v a) -> Maybe a
solveFunDirect = fmap (uncurry $ flip runEvalM) . runFunDirect

runFunDirect :: (HasTrie id, Ord id, Show id
                ,Bounded v, Enum v, Ord v, Show v
                ,HasTrie v, HasTrie tv, Show tv) =>
                SAT id tv v a -> Maybe (a, BIEnv v)
runFunDirect (SAT m) = let
    (val, St _ circuit _weighted) = runState m st0

    -- Skip weighted booleans as Funsat does not do weighted SAT
    circuitProb = toCNF  (runShared circuit)
    (sol,_,_)   = Funsat.solve1 $ rpoProblemCnf circuitProb

  in case sol of
       Sat{}   -> Just (val, projectRPOCircuitSolution sol circuitProb)
       Unsat{} -> Nothing

runFun :: (HasTrie id, Ord id, Bounded v, Enum v, Ord v, HasTrie v, HasTrie tvar, Show v) =>
          SAT id tvar v a -> Maybe (a, BIEnv v)
runFun (SAT m) = let
    (val, St pool circuit _weighted) = runState m st0

    -- Skip weighted booleans as Funsat does not do weighted SAT
    (circuitProb, natbits) = toCNF' pool (runShared circuit)
    (sol,_,_)   = Funsat.solve1 (eproblemCnf circuitProb)

  in case sol of
       Sat{}   -> Just (val, reconstructNatsFromBits (Trie.toList natbits) $ projectECircuitSolution sol circuitProb)
       Unsat{} -> Nothing
