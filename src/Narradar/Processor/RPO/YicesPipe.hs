{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Narradar.Processor.RPO.YicesPipe where

import Control.Applicative
import Control.DeepSeq
import Control.Exception as CE (assert)
import Control.Monad
import Control.Parallel.Strategies
import Data.Bifunctor
import Data.Foldable as F (Foldable, toList)
import Data.Traversable (Traversable)
import Data.Hashable
import Data.Suitable (Suitable)
import Data.Typeable
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import Data.Monoid (Monoid(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Term.Family as Family
import Prelude.Extras

import Narradar.Framework.GraphViz

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..))
import qualified Narradar.Constraints.SAT.YicesCircuit as Yices
import Narradar.Constraints.SAT.MonadSAT( Decode(..),Tree,printTree, mapTreeTerms )
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Constraints.SAT.RPOAF ( UsableSymbol(..), MkSATSymbol
                                      , RPOSsymbol(..), RPOsymbol(..), LPOSsymbol, LPOsymbol, MPOsymbol
                                      , RPOProblemN, RPOId
                                      , UsableSymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, rpoAF_IGDP'
                                      , theSymbolR, isUsable, usableSymbol, filtering, status
                                      , verifyRPOAF, isCorrect
                                      , omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone)
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Processor.RPO
import Narradar.Utils
import System.IO.Unsafe
import qualified Debug.Trace
import qualified Funsat.TermCircuit as RPOAF

import Debug.Hoed.Observe

solve = Yices.solve MonadSAT.V

-- -------------------
-- RPO SAT Processor
-- -------------------

instance ( Info info (RPOProof id)
         , Info info (Problem (Constant Rewriting (TermF id)) (NTRS id))
         , FrameworkId id, Show id
--         , FrameworkProblemN (Constant Rewriting (TermN id)) id
         ) => Processor (RPOProc info) (NProblem Rewriting id)
   where
    type Typ (RPOProc info) (NProblem Rewriting id) = Rewriting
    type Trs (RPOProc info) (NProblem Rewriting id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules allowCol) p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol) p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol) p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol) p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol) p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.mpo)


instance (FrameworkId id
         ,Info info (RPOProof id)
         ,Info info (Problem (Constant IRewriting (TermF id)) (NTRS id))
--         ,FrameworkProblemN (Constant IRewriting (TermN id)) id
         ) => Processor (RPOProc info) (NProblem IRewriting id)
   where
    type Typ (RPOProc info) (NProblem IRewriting id) = IRewriting
    type Trs (RPOProc info) (NProblem IRewriting id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules allowCol)    p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    p = procAF' p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.mpo)


instance (FrameworkId id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (QRewritingN id) id)
   where
    type Typ (RPOProc info) (NProblem (QRewritingN id) id) = QRewritingN id
    type Trs (RPOProc info) (NProblem (QRewritingN id) id) = NTRS id
    applyO _ (RPOProc RPOSAF usablerules allowCol)    p = procAF p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    p = procAF p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    p = procAF p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    p = procAF p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    p = procAF p usablerules ((solve.) . rpoAF_DP allowCol RPOAF.mpo)

instance (Info info (RPOProof id)
         ,FrameworkProblemN (InitialGoal (TermF id) Rewriting) id
         ,DPSymbol id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = InitialGoal (TermF id) Rewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) Rewriting) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules allowCol)    p = procAF_IG p usableRules ((solve.)   . rpoAF_IGDP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    p = procAF_IG p usablerules ((solve.)   . rpoAF_IGDP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    p = procAF_IG p usablerules ((solve.)   . rpoAF_IGDP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    p = procAF_IG p usablerules ((solve.)   . rpoAF_IGDP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    p = procAF_IG p usablerules ((solve.)   . rpoAF_IGDP allowCol RPOAF.mpo)

instance (Info info (RPOProof id)
         ,Info info (NProblem IRewriting id)
         ,Info info (Problem (Constant IRewriting (TermF id)) (NTRS id))
         ,FrameworkProblemN IRewriting id
--         ,FrameworkProblemN (Constant IRewriting (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) IRewriting) id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = InitialGoal (TermF id) IRewriting
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) IRewriting) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules allowCol)    = liftProblem $ \p -> procAF' p usableRules ((solve.) . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.mpo)

instance (FrameworkId id, DPSymbol id, GenSymbol id
         ,Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = InitialGoal (TermF id) NarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) NarrowingGen) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules allowCol)    p = procAF_IGgen p usableRules ((solve.)   . rpoAF_IGDP' allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    p = procAF_IGgen p usablerules ((solve.)   . rpoAF_IGDP' allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    p = procAF_IGgen p usablerules ((solve.)   . rpoAF_IGDP' allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    p = procAF_IGgen p usablerules ((solve.)   . rpoAF_IGDP' allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    p = procAF_IGgen p usablerules ((solve.)   . rpoAF_IGDP' allowCol RPOAF.mpo)

instance (Info info (RPOProof id)
         ,Info info (NProblem INarrowingGen id)
         ,Info info (Problem (Constant INarrowingGen (TermF id)) (NTRS id))
         ,FrameworkProblemN INarrowingGen id
--         ,FrameworkProblemN (Constant INarrowingGen (TermN id)) id
         ,FrameworkProblemN (InitialGoal (TermF id) INarrowingGen) id
         ,GenSymbol id
         ) => Processor (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id)
   where
    type Typ (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = InitialGoal (TermF id) INarrowingGen
    type Trs (RPOProc info) (NProblem (InitialGoal (TermF id) INarrowingGen) id) = NTRS id
    applyO _ (RPOProc RPOSAF usableRules allowCol)    = liftProblem $ \p -> procAF' p usableRules ((solve.)   . rpoAF_DP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    = liftProblem $ \p -> procAF' p usablerules ((solve.)   . rpoAF_DP allowCol RPOAF.mpo)

instance (Info info (RPOProof id)
         ,FrameworkId id
         ) => Processor (RPOProc info) (NProblem Narrowing id)
  where
    type Typ (RPOProc info) (NProblem Narrowing id) = Narrowing
    type Trs (RPOProc info) (NProblem Narrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    applyO _ (RPOProc RPOSAF usableRules allowCol)    p = procNAF p usableRules ((solve.)   . rpoAF_NDP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.mpo)

instance (FrameworkId  id
         ,Info info (RPOProof id)
         ) => Processor (RPOProc info) (NProblem CNarrowing id)
  where
    type Typ (RPOProc info) (NProblem CNarrowing id) = CNarrowing
    type Trs (RPOProc info) (NProblem CNarrowing id) = NTRS id
   -- FIXME: I don't see why we cannot have collapsing filterings here. Enable and test
    applyO _ (RPOProc RPOSAF usableRules allowCol)    p = procNAF p usableRules ((solve.)   . rpoAF_NDP allowCol RPOAF.rpos)
    applyO _ (RPOProc RPOAF  usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.rpo)
    applyO _ (RPOProc LPOSAF usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.lpos)
    applyO _ (RPOProc LPOAF  usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.lpo)
    applyO _ (RPOProc MPOAF  usablerules allowCol)    p = procNAF p usablerules ((solve.)   . rpoAF_NDP allowCol RPOAF.mpo)
