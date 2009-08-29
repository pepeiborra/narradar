{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Narradar.Processor.InitialGoalNarrowingProblem where

import Data.Monoid

import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGoal

-- This is the approach of Alpuente, Escobar, Iborra in ICLP'08
data InitialGoalNarrowingToNarrowingGoal = InitialGoalNarrowingToNarrowingGoal deriving (Eq, Show)

-- This is the approach used for termination of logic programs by Schneider-Kamp et al.
-- It is also applicable to narrowing, however it has not been formalized anywhere.
-- But an equivalent approach is formalized by Vidal in FLOPS'08
data InitialGoalNarrowingToInfinitaryRewriting = InitialGoalNarrowingToInfinitaryRewriting deriving (Eq, Show)

-- This is the approach of Iborra, Nishida & Vidal
data InitialGoalNarrowingToRelativeRewriting = InitialGoalNarrowingToRelativeRewriting deriving (Eq, Show)

instance (Ord id, HasSignature trs) =>
    Processor InitialGoalNarrowingToNarrowingGoal trs (InitialGoal id Narrowing) (NarrowingGoal id) where
  apply _ p = mprod [mkNewProblem (narrowingGoal g) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

instance (Ord id, HasSignature trs) =>
    Processor InitialGoalNarrowingToNarrowingGoal trs (InitialGoal id CNarrowing) (CNarrowingGoal id) where
  apply _ p = mprod [mkNewProblem (cnarrowingGoal g) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p


instance (Ord id, HasSignature trs) =>
    Processor InitialGoalNarrowingToInfinitaryRewriting trs (InitialGoal id Narrowing) (Infinitary id Rewriting) where
  apply _ p = mprod [mkNewProblem (infinitary g Rewriting) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

instance (Ord id, HasSignature trs) =>
    Processor InitialGoalNarrowingToInfinitaryRewriting trs (InitialGoal id CNarrowing) (Infinitary id IRewriting) where
  apply _ p = mprod [mkNewProblem (infinitary g IRewriting) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p
