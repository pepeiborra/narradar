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
    , Var, VarMaps(..)
    ) where

import           Control.Applicative
import           Control.Arrow                            (first,second)
import           Control.DeepSeq                          (rnf)
import           Control.Exception                        (evaluate, try, SomeException)
import           Control.Monad.RWS                        (RWST(..), MonadReader(..), runRWST)
import           Control.Monad.State
import           Data.Array.Unboxed
import qualified Data.HashMap                             as Trie
import           Data.List                                (unfoldr)
import           Data.Monoid                              (Monoid(..), (<>))
import           Data.Hashable
import           Data.Term.Rules                          (getAllSymbols)
import           Funsat.Types                             (Solution(Sat), numVars, numClauses, clauses)
import           Funsat.Circuit                           (BEnv, and,or,not, orL)
import           Funsat.ECircuit                          (eproblemCnf, projectECircuitSolution)
import           Funsat.RPOCircuit
import           Funsat.RPOCircuit.Symbols                (Natural(..))
import           Funsat.RPOCircuit.Internal
import           System.Directory
import           System.FilePath
import           System.IO
import           System.IO.Unsafe
import           System.Process
import           System.TimeIt
import           Text.Printf

import           Narradar.Constraints.SAT.MonadSAT        hiding (and,or)
import           Narradar.Framework                       (TimeoutException(..))
import           Narradar.Utils                           ( debug, debug', echo, echo', readProcessWithExitCodeBS )
import           Narradar.Types                           ( TermN )

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

type k :->: v = Trie.HashMap k v

data VarMaps expr id var = VarMaps
    { termGtMap :: !((TermN id, TermN id) :->: expr)
    , termGeMap :: !((TermN id, TermN id) :->: expr)
    , termEqMap :: !((TermN id, TermN id) :->: expr)
    }
  deriving Show

instance Ord id => Monoid (VarMaps expr id var) where
 mempty = VarMaps mempty mempty mempty
 mappend (VarMaps gt1 ge1 eq1) (VarMaps gt2 ge2 eq2) =
   VarMaps (gt1 <> gt2) (ge1 <> ge2) (eq1 <> eq2)

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
