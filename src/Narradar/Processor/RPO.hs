{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Narradar.Processor.RPO where

import Control.Applicative
import Control.DeepSeq
import Control.Exception as CE (assert)
import Control.Monad
import Control.Parallel.Strategies
import Data.Bifunctor
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.NarradarTrie (HasTrie)
import Data.Typeable
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set

import Narradar.Framework.GraphViz

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO
import Narradar.Constraints.SAT.Solve ( SAT, EvalM, BIEnv, runEvalM, decode, Var
                                      , smtSerial, smtFFI, satYices, YicesOpts(..))
import Narradar.Constraints.SAT.RPOAF ( SymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP
                                      , isUsable, theSymbolR, filtering
                                      , verifyRPOAF, isCorrect)
--import Narradar.Constraints.SAT.RPO   (verifyRPO)
--import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import qualified Narradar.Constraints.SAT.RPOAF.Symbols ()
import Narradar.Utils
import System.IO.Unsafe
import qualified Debug.Trace

-- -------------------
-- RPO SAT Processor
-- -------------------
--rpo :: (MonadPlus mp, Info info i, Info info o, Processor info RPOProc i o) =>
--       i -> Proof info mp o
--rpo = apply (RPOProc RPOSAF SMTSerial)

runSAT :: (HasTrie id, Ord id, Show id) => SATSolver -> SAT id Narradar.Var Var (EvalM Var a) -> IO (Maybe a)
runSAT Yices = satYices YicesOpts{maxWeight = 20, timeout = Nothing}
-- runS FunSat = solveFun
-- runS FunSatDirect = solveFunDirect
-- runS (Yices1 timeout) = unsafePerformIO . solveYicesDirect YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp  timeout) = unsafePerformIO . solveYicesSimp YicesOpts{maxWeight = 20, timeout = Just 60}
-- runS (YicesSimp1 timeout) = unsafePerformIO . solveYicesSimp1 YicesOpts{maxWeight = 20, timeout = Just 60}

data RPOProc   = RPOProc Extension Solver
data Extension = RPOSAF | RPOAF | LPOSAF | MPOAF | LPOAF --  | LPOS | LPO | MPO
data Solver    = SMTFFI | SMTSerial | SAT SATSolver
data SATSolver = Yices | Minisat | Funsat


instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem Rewriting id)
                             (NProblem Rewriting id)
   where

    apply (RPOProc RPOSAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.rpo p)

    apply (RPOProc LPOAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.lpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.lpos p)

    apply (RPOProc MPOAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.mpo p)

instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem IRewriting id)
                             (NProblem IRewriting id)
   where

    apply (RPOProc RPOSAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.rpo p)

    apply (RPOProc LPOAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.lpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.lpos p)

    apply (RPOProc MPOAF  SMTFFI)        p = procAF p (smtFFI       $ rpoAF_DP True RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procAF p (smtSerial $ rpoAF_DP True RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procAF p (runSAT s     $ rpoAF_DP True RPOAF.mpo p)

instance (Show id, Ord id, Pretty id, DPSymbol id, HasTrie id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) Rewriting) id)
                             (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    apply (RPOProc RPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpos p)

    apply (RPOProc LPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpo p)

    apply (RPOProc MPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.mpo p)

instance (Show id, Ord id, Pretty id, DPSymbol id, HasTrie id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) IRewriting) id)
                             (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    apply (RPOProc RPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpos p)

    apply (RPOProc LPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpo p)

    apply (RPOProc MPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.mpo p)

instance (Show id, Ord id, Pretty id, DPSymbol id, HasTrie id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) NarrowingGen) id)
                             (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    apply (RPOProc RPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpos p)

    apply (RPOProc LPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpo p)

    apply (RPOProc MPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.mpo p)

instance (Show id, Ord id, Pretty id, DPSymbol id, HasTrie id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) CNarrowingGen) id)
                             (NProblem (InitialGoal (TermF id) CNarrowingGen) id)
   where
    apply (RPOProc RPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpos p)
--    apply (RPOProc RPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.rpo p)
--    apply (RPOProc RPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.rpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpos p)
--    apply (RPOProc LPOSAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpos p)

    apply (RPOProc LPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.lpo p)
--    apply (RPOProc LPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.lpo p)

    apply (RPOProc MPOAF  SMTFFI)        p = procAF_IG p (smtFFI       $ rpoAF_IGDP True RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procAF_IG p (smtSerial $ rpoAF_IGDP True RPOAF.mpo p)
--    apply (RPOProc MPOAF (SAT s))        p = procAF_IG p (runSAT s     $ rpoAF_IGDP True RPOAF.mpo p)

instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem Narrowing id)
                             (NProblem Narrowing id)
  where
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    apply (RPOProc RPOSAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.rpo p)

    apply (RPOProc LPOAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.lpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.lpos p)

    apply (RPOProc MPOAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.mpo p)

instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                        (NProblem CNarrowing id)
                        (NProblem CNarrowing id)
  where
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    apply (RPOProc RPOSAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc RPOSAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc RPOSAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.rpos p)

    apply (RPOProc RPOAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.rpo p)
    apply (RPOProc RPOAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.rpo p)
    apply (RPOProc RPOAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.rpo p)

    apply (RPOProc LPOAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.lpo p)
    apply (RPOProc LPOAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.lpo p)
    apply (RPOProc LPOAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.lpo p)

    apply (RPOProc LPOSAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOSAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOSAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.lpos p)

    apply (RPOProc MPOAF  SMTFFI)        p = procNAF p (smtFFI       $ rpoAF_NDP False RPOAF.mpo p)
    apply (RPOProc MPOAF SMTSerial) p = procNAF p (smtSerial $ rpoAF_NDP False RPOAF.mpo p)
    apply (RPOProc MPOAF (SAT s))        p = procNAF p (runSAT s     $ rpoAF_NDP False RPOAF.mpo p)

-- -----------------
-- Implementations
-- -----------------

wsatYices tm = satYices YicesOpts{maxWeight = 20, timeout = Just tm}
{-
procAF :: (Monad m
          ,sres  ~ SymbolRes id
          ,Info info (NProblem typ id)
          ,Info info (RPOProof id)
          ,Pretty id, Ord id, HasTrie id
          ,Traversable  (Problem typ)
          ,MkDPProblem typ (NTRS id)
          )=> NProblem typ id -> (IO (Maybe ([Int], BIEnv))) -> Proof info m (NProblem typ id)
-}
procAF p = f . unsafePerformIO where
 f Nothing = dontKnow (rpoFail p) p
 f (Just (nondec_dps, bienv, symbols_raw)) = singleP proof p p'
  where
   symbols       = runEvalM bienv $ mapM decode symbols_raw
   proof         = RPOAFProof decreasingDps usableRules symbols
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
   p'            = setP (restrictTRS dps nondec_dps) p
{-
   verification  = forDPProblem verifyRPOAF p symbols nondec_dps
   isValidProof
     | isCorrect verification = True
     | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False

   CE.assert isValidProof $
-}

procAF_IG p = f . unsafePerformIO where
 f Nothing = dontKnow (rpoFail p) p
 f (Just (nondec_dps, bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p)
  where
   symbols       = runEvalM bienv $ mapM decode symbols_raw
   proof         = RPOAFProof decreasingDps usableRules symbols
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
{-
   verification  = runEvalM bienv $ verifyRPOAF typSymbols rrSymbols dpsSymbols nondec_dps
   typSymbols    = mapInitialGoal (bimap convertSymbol id) (getProblemType p)
   rrSymbols     = mapNarradarTRS (mapTermSymbols convertSymbol) (getR p)
   dpsSymbols    = mapNarradarTRS (mapTermSymbols convertSymbol) (getP p)
   convertSymbol = fromJust . (`Map.lookup` Map.fromList
                                            [(theSymbolR(runEvalM bienv $ decode s), s)
                                                 | s <- symbols_raw])
   isValidProof
    | isCorrect verification = True
    | otherwise = Debug.Trace.trace (show (proof $+$ Ppr.empty $+$ verification)) False
-}

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
procNAF p = f . unsafePerformIO where
 f Nothing = dontKnow (rpoFail p) p
 f (Just ((non_dec_dps, non_rhsground_dps), bienv, symbols_raw)) =
    let proof = RPOAFProof decreasingDps usableRules symbols
        symbols       = runEvalM bienv $ mapM decode symbols_raw
        decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ non_dec_dps) (rules dps)
        usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
        usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
        p1            = setP (restrictTRS dps non_dec_dps) p
        p2            = setP (restrictTRS dps non_rhsground_dps) p
    in andP proof p (snub [p1,p2])
       where dps = getP p
{-
proc :: ( Pretty id
        , Info info (RPOProof id), Info info (NarradarProblem typ t)
        , IsDPProblem typ, Monad m
        ) =>
        NarradarProblem typ t -> IO (Maybe ([Int], [RPO.SymbolRes id]))
     -> Proof info m (NarradarProblem typ t)

proc p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (nondec_dps, symbols) ->
                      let proof         = RPOProof decreasingDps [] symbols
                          dps           = getP p
                          decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
                          p'            = setP (restrictTRS dps nondec_dps) p
                          verification  = verifyRPO p symbols nondec_dps
                          isValidProof
                            | isCorrect verification = True
                            | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False
                      in
                         CE.assert isValidProof $
                         singleP proof p p'
-}
-- -------------
-- RPO Proofs
-- -------------

data RPOProof id where
     RPOAFProof :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [RPOAF.SymbolRes id]
                -> RPOProof id
{-
     RPOProof   :: Pretty (Rule t v) =>
                   [Rule t v]       --  ^ Strictly Decreasing dps
                -> [Rule t v]       --  ^ Usable Rules
                -> [RPO.SymbolRes id]
                -> RPOProof id
-}
     RPOFail :: RPOProof id

rpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> RPOProof (TermId t)
rpoFail _ = RPOFail

instance (Ord id, Pretty id) => Pretty (RPOProof id) where
    pPrint (RPOAFProof dps rr ss) =
        text "RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "The argument filtering used was:" $$
        nest 4 (pPrint the_af) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map pPrint rr) $$
        text "Precedence:" <+> printPrec RPOAF.precedence RPOAF.theSymbolR ssPrec $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPOAF.SymbolRes{..} <- ssPrec])
     where
       the_af = AF.fromList' [(theSymbolR, filtering) | RPOAF.SymbolRes{..} <- ss]
       relevantSymbols = getAllSymbols (dps `mappend` rr)
       ssPrec = [ s | s <- ss, theSymbolR s `Set.member` relevantSymbols]
{-
    pPrint (RPOProof dps _ ss) =
        text "Monotonic RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "Precedence:" <+> printPrec RPO.precedence RPO.theSymbolR ss $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPO.SymbolRes{..} <- ss])
-}
    pPrint RPOFail = text "RPO Reduction Pair : failed to synthetize a suitable ordering"


printPrec f symb    = fsep
                    . punctuate (text " >")
                    . fmap ( fsep
                           . punctuate (text (" ="))
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)