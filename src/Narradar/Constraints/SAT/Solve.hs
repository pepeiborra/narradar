{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- LANGUAGE NoMonoLocalBinds #-}

module Narradar.Constraints.SAT.Solve
    ( BIEnv, EvalM, runEvalM
    , module Narradar.Constraints.SAT.Solve
    , Var
    ) where

import Bindings.Yices ( Context, mkContext, interrupt, setVerbosity, assertWeighted
                      , setLogFile, delContext, isInconsistent)
import           Control.Applicative
import           Control.Arrow                            (first,second)
import           Control.DeepSeq                          (rnf)
import           Control.Exception                        (evaluate, try, SomeException)
import           Control.Monad.RWS                        (RWST(..), MonadReader(..), runRWST)
import           Control.Monad.State
import           Data.Array.Unboxed
import           Data.List                                (unfoldr)
import           Data.Monoid                              (Monoid(..))
import           Data.Hashable
import           Data.Term.Rules                          (getAllSymbols)
import           Funsat.Types                             (Solution(Sat), numVars, numClauses, clauses)
import           Funsat.Circuit                           (BEnv, and,or,not, orL)
import           Funsat.ECircuit                          (eproblemCnf, projectECircuitSolution)
import           Funsat.RPOCircuit
import           Funsat.RPOCircuit.Symbols                (Natural(..))
import           Funsat.RPOCircuit.Internal
import           Math.SMT.Yices.Syntax
import           System.Directory
import           System.FilePath
import           System.IO
import           System.IO.Unsafe
import           System.Process
import           System.TimeIt
import           Text.Printf

import           Narradar.Constraints.SAT.MonadSAT        hiding (and,or)
import           Narradar.Constraints.SAT.YicesCircuit    as Serial (YicesSource, YMaps(..), emptyYMaps, runYices', generateDeclarations, solveDeclarations)
import           Narradar.Constraints.SAT.YicesFFICircuit as FFI    (YicesSource, YMaps(..), emptyYMaps, computeBIEnv, runYicesSource)
import           Narradar.Framework                       (TimeoutException(..))
import           Narradar.Framework.Ppr
import           Narradar.Utils                           ( debug, debug', echo, echo', readProcessWithExitCodeBS )
import           Narradar.Types                           ( TermN )

import qualified Bindings.Yices                           as Yices
import qualified Control.Exception                        as CE
import qualified Data.ByteString.Char8                    as BS
import qualified Data.ByteString.Lazy.Char8               as LBS
import qualified Data.HashMap                             as HashMap
import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set
import qualified Funsat.Types                             as Funsat
import qualified Funsat.RPOCircuit                        as RPOCircuit
import qualified Narradar.Types                           as Narradar

import           Prelude                                  hiding (and, not, or, any, all, lex, (>))
import qualified Prelude                                  as P

-- ----------------------------
-- SMT MonadSAT implementation
-- ----------------------------

-- *** serialized

data StY id v = StY { poolY :: [Int]
                    , mkV   :: Maybe String -> Int -> v
                    , cmdY  :: [CmdY]
                    , stY   :: Serial.YMaps id v
                    }

newtype SMTY id v a = SMTY {unSMTY :: State (StY id v) a} deriving (Functor, Monad, MonadState (StY id v))

smtSerial :: (Hashable id, Ord id, Show id, Pretty id, Enum v, Ord v, Read v, Show v) =>
             (Maybe String -> Int -> v) -> SMTY id v (EvalM v a) -> IO (Maybe a)
smtSerial mkVar (SMTY my) = do
  let (me, StY{..}) = runState my (StY [toEnum 1000 ..] mkVar [] Serial.emptyYMaps)
--  let symbols = getAllSymbols $ mconcat [ Set.fromList [t, u] | ((t,u),_) <- HashMap.toList (termGtMap stY) ++ HashMap.toList (termEqMap stY)]
  bienv <- solveDeclarations Nothing (generateDeclarations stY ++ cmdY)
--  debug (unlines $ map show $ Set.toList symbols)
  debug (show . vcat . map (uncurry printGt.second fst) . HashMap.toList . Serial.termGtMap $ stY)
  debug (show . vcat . map (uncurry printEq.second fst) . HashMap.toList . Serial.termEqMap $ stY)
  return ( (`runEvalM` me) <$> bienv )
 where
  printEq (t,u) v = v <> colon <+> t <+> text "=" <+> u
  printGt (t,u) v = v <> colon <+> t <+> text ">" <+> u

instance (Hashable v, Ord v, Show v) => MonadSAT (Serial.YicesSource id) v (SMTY id v) where
  boolean_ "" = do {st@StY{poolY = h:t, mkV} <- get; put st{poolY=t}; return (mkV Nothing h)}
  boolean_ s = do {st@StY{poolY = h:t, mkV} <- get; put st{poolY=t}; return (mkV (Just s) h)}
  natural_ s = do {b <- boolean_ s; return (Natural b)}
  assert_ _ [] = return ()
  assert_ msg a = do
      st <- gets stY
      let (me, stY') = runYices' st $ foldr or false a
      modify $ \st -> st{cmdY = ASSERT me : cmdY st, stY = stY'}

  assertW w a = do
      st <- gets stY
      let (me, st') = runYices' st $ foldr or false a
      modify $ \st -> st{cmdY = ASSERT_P me (Just $ fromIntegral w) : cmdY st, stY = st'}
      return ()
-- *** FFI

data StY' id v = StY' { poolY' :: ![v]
                      , stY'   :: !(FFI.YMaps id v)
                      }

newtype SMTY' id v a = SMTY' {unSMTY' :: RWST Context () (StY' id v) IO a}
    deriving (Functor, Monad, MonadIO, MonadReader Context, MonadState (StY' id v))

smtFFI :: (Enum v, Ord v, Show v, Hashable v
          ,Hashable id, Ord id, Show id, Pretty id
          ) => SMTY' id v (EvalM v a) -> IO (Maybe a)
smtFFI = smtFFI' 1
smtFFI' start (SMTY' my) = do
  ctx <- mkContext
#ifdef DEBUG
--  setVerbosity 10
  setLogFile "yices.log"
#endif
  (me, StY'{stY'}, _) <- runRWST my ctx (StY' [toEnum start ..] FFI.emptyYMaps)
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


instance (Enum v, Ord v, Show v, Hashable v) => MonadSAT (FFI.YicesSource id) v (SMTY' id v) where
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

-- ------------------------------------------
-- Boolean Circuits MonadSAT implementation
-- ------------------------------------------
data St term v = St { pool     :: [v]
                    , circuit  :: !(Shared term Narradar.Var v)
                    , weightedClauses :: [(Weight, Clause)]}

newtype SAT term v a = SAT {unSAT :: State (St term v) a} deriving (Functor, Monad, MonadState (St term v))

instance (Ord v, Hashable v, Show v) => MonadSAT (Shared term Narradar.Var) v (SAT term v) where
  boolean_ _ = do {st@St{pool = h:t} <- get; put st{pool=t}; return h}
  natural_ _ = do {b <- boolean; return (Natural b)}
  assert_ _ [] = return ()
  assert_ _  a = do {st <- get; put st{circuit = orL a `and` circuit st}}
  assertW  w a = return () -- = do {st <- get; put st{weightedClauses = ( w, a) : weightedClauses st}}

st0 = St [minBound..] true []


-- *** SAT based (using Yices) solver

data YicesOpts = YicesOpts {maxWeight :: Int, timeout :: Maybe Int}
defaultYicesOpts = YicesOpts 0 Nothing

satYices :: (Hashable id, Ord id, Show id
            ,Ord v, Show v, Hashable v, Enum v
            ) =>
            YicesOpts -> SAT (Narradar.TermF id) v (EvalM v a) -> IO (Maybe a)
satYices = satYices' 1
satYices' start yo (SAT m) = do
  let (val, St _ circuit weighted) = runState m (St [toEnum start ..] true [])
  let circuitProb = toCNF(runShared circuit)
  mb_sol <- solveYices yo (rpoProblemCnf circuitProb) weighted
  return $ fmap (\sol -> runEvalM (projectRPOCircuitSolution sol circuitProb) val) mb_sol

satYicesSimp = satYicesSimp' 1
satYicesSimp' start yo (SAT m) = do
  let (val, St pool circuit weighted) = runState m (St [toEnum start..] true [])
      (circuitProb, natbits) = toCNF' pool (runShared circuit)

  mb_sol <- solveYices yo (eproblemCnf circuitProb) weighted
  return $ do
    sol <- mb_sol
    let bienv = reconstructNatsFromBits (HashMap.toList natbits) $ projectECircuitSolution sol circuitProb
    return $ runEvalM bienv val

solveYices YicesOpts{..} cnf weighted = do
    let nv            = numVars cnf
        nc            = numClauses cnf

    -- feed the problem to Yices
        cs     = map (\c -> unwords (show maxWeight : map show c ++ ["0"] ))
                     (clauses cnf)
        wcs    = map (\(w,c) -> unwords (show w : map show c ++ ["0"]))
                     weighted
        header = printf "p wcnf %d %d %d" nv (nc + length wcs) maxWeight
        opts =  ["-e","-d","-ms", "-mw", show maxWeight] ++ maybe [] (\t -> ["-tm", show t]) timeout

    evaluate (rnf cs)
    debug' "Calling Yices..."
    ( code, the_stdout, the_stderr ) <- readProcessWithExitCode "yices" opts (unlines $ header : wcs ++ cs)
    debug "done"
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

-- -- *** Funsat solver by simplification to vanilla Circuits

-- solveFun :: ( Hashable id, Ord id, Bounded v
--             , Enum v, Show v, Ord v, Hashable v
--             , Ord tv, Hashable tv, Show tv) =>
--             SAT id tv v (EvalM v a) -> Maybe a
-- solveFun = fmap (uncurry $ flip runEvalM) . runFun

-- solveFunDirect :: ( Hashable id, Ord id, Show id
--                   , Bounded v, Enum v, Hashable v, Ord v, Show v
--                   , Hashable tv, Ord tv, Show tv) =>
--                   SAT id tv v (EvalM v a) -> Maybe a
-- solveFunDirect = fmap (uncurry $ flip runEvalM) . runFunDirect

-- runFunDirect :: (Hashable id, Ord id, Show id
--                 ,Bounded v, Enum v, Ord v, Show v
--                 ,Hashable v, Hashable tv, Ord tv, Show tv) =>
--                 SAT id tv v a -> Maybe (a, BIEnv v)
-- runFunDirect (SAT m) = let
--     (val, St _ circuit _weighted) = runState m st0

--     -- Skip weighted booleans as Funsat does not do weighted SAT
--     circuitProb = toCNF  (runShared circuit)
--     (sol,_,_)   = Funsat.solve1 $ rpoProblemCnf circuitProb

--   in case sol of
--        Sat{}   -> Just (val, projectRPOCircuitSolution sol circuitProb)
--        Unsat{} -> Nothing

-- runFun :: (Hashable id, Ord id, Bounded v, Enum v, Ord v, Hashable v, Hashable tvar, Ord tvar, Show v) =>
--           SAT id tvar v a -> Maybe (a, BIEnv v)
-- runFun (SAT m) = let
--     (val, St pool circuit _weighted) = runState m st0

--     -- Skip weighted booleans as Funsat does not do weighted SAT
--     (circuitProb, natbits) = toCNF' pool (runShared circuit)
--     (sol,_,_)   = Funsat.solve1 (eproblemCnf circuitProb)

--   in case sol of
--        Sat{}   -> Just (val, reconstructNatsFromBits (HashMap.toList natbits) $ projectECircuitSolution sol circuitProb)
--        Unsat{} -> Nothing
