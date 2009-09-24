{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Narradar.Processor.InitialGoalNarrowingProblem where

import Control.Applicative
import Data.Foldable (Foldable, toList)
import Data.List ((\\))
import Data.Monoid
import Data.Term
import TRSTypes (Mode(..))

import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Types hiding (term, Term)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Types.Problem.NarrowingGen as Gen
import Narradar.Utils

-- | This is the approach of Alpuente, Escobar, Iborra in ICLP'08
data InitialGoalNarrowingToNarrowingGoal = InitialGoalNarrowingToNarrowingGoal deriving (Eq, Show)

-- | This is the approach used for termination of logic programs by Schneider-Kamp et al.
--   It is also applicable to narrowing, however it has not been formalized anywhere.
--   But an equivalent approach is formalized by Vidal in FLOPS'08
data InitialGoalNarrowingToInfinitaryRewriting = InitialGoalNarrowingToInfinitaryRewriting deriving (Eq, Show)

-- | This is the approach of Iborra, Nishida & Vidal
data InitialGoalNarrowingToRelativeRewriting = InitialGoalNarrowingToRelativeRewriting deriving (Eq, Show)

instance (HasId t, Foldable t, TermId t ~ id, SignatureId trs ~ id, Ord id, Ord (Term t Var), HasSignature trs) =>
    Processor InitialGoalNarrowingToNarrowingGoal
              (DPProblem (InitialGoal t Narrowing) trs)
              (DPProblem (NarrowingGoal id) trs)
 where
  apply _ p = mprod [mkDerivedProblem (narrowingGoal g) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

instance (HasId t, Foldable t, TermId t ~ id, Ord id, Ord (Term t Var), HasSignature trs, SignatureId trs ~ id) =>
    Processor InitialGoalNarrowingToNarrowingGoal
              (DPProblem (InitialGoal t CNarrowing) trs)
              (DPProblem (CNarrowingGoal id) trs)
 where
  apply _ p = mprod [mkDerivedProblem (cnarrowingGoal g) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p


instance (HasId t, Foldable t, Ord (Term t Var), TermId t ~ id, Ord id, HasSignature trs, SignatureId trs ~ id) =>
    Processor InitialGoalNarrowingToInfinitaryRewriting
              (DPProblem (InitialGoal t Narrowing) trs)
              (DPProblem (Infinitary id Rewriting) trs)
 where
  apply _ p = mprod [mkDerivedProblem (infinitary g Rewriting) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

instance (HasId t, Foldable t, Ord (Term t Var), TermId t ~ id, Ord id, HasSignature trs, SignatureId trs ~ id) =>
    Processor InitialGoalNarrowingToInfinitaryRewriting
              (DPProblem (InitialGoal t CNarrowing) trs)
              (DPProblem (Infinitary id IRewriting) trs)
 where
  apply _ p = mprod [mkDerivedProblem (infinitary g IRewriting) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

{-
instance (trsGDP ~ NarradarTRS gdp Var
         ,gid    ~ GenTermF id
         ,gdp    ~ GenTermF (Identifier id)
         ,typ'   ~ InitialGoal gdp (Relative trsGDP NarrowingGen)
--         ,MkNarradarProblem (InitialGoal gdp (Relative trsGDP NarrowingGen)) gid
         ,Ord id
         ) =>
    Processor InitialGoalNarrowingToRelativeRewriting
              (DPProblem (InitialGoal (TermF (Identifier id)) Narrowing) (NTRS (Identifier id) Var))
              (DPProblem (InitialGoal (GenTermF (Identifier id))
                                      (Relative (NarradarTRS (GenTermF (Identifier id)) Var) NarrowingGen))
                         (NarradarTRS (GenTermF (Identifier id)) Var))
 where
   apply = initialGoalNarrowingToRelativeRewriting
-}
initialGoalNarrowingToRelativeRewriting ::
              forall typ typ' tag id mp gid gdp trsG trsGDP.
            ( gid ~ GenTermF id
            , gdp ~ GenTermF (Identifier id)
            , typ' ~ InitialGoal gdp (Relative trsGDP NarrowingGen)
            , trsG ~ NarradarTRS gid Var
            , trsGDP ~ NarradarTRS gdp Var
            , Ord id, Pretty (Identifier id)
--            ,MkDPProblem (Relative trs NarrowingGen) trsGDP
            , Monad mp
            ) => tag -> DPProblem (InitialGoal (TermF (Identifier id)) Narrowing) (NarradarTRS (TermF (Identifier id)) Var)
                     -> Proof mp (DPProblem typ' trsGDP)

initialGoalNarrowingToRelativeRewriting _ p =
              mprod [mkNewProblem (initialGoal [goal] (relative genRules narrowingGen))
                                  (tRS (goalRule : rr') :: trsG)
                      | Goal f modes <- gg
                      , let rr' = convert <$$> (rules $ getR p)
                      , let goal_vars =  [ v | (G,v) <- modes `zip` take (length modes) vars]
                      , let goalRule = goalTerm goal_vars :-> term (symbol f) (take (length modes) vars)
                    , let goal = Goal (GoalId :: GenId (Identifier id)) []
                    ]
    where
      vars = map return ([toEnum 0 ..] \\ toList (getVars p))
      InitialGoal gg gr p0 = getProblemType p
      convert  = mapTerm (\(Narradar.Term id tt) -> Gen.Term (symbol id) tt)
      genRules = tRS [ genTerm :-> Gen.term c (replicate ar genTerm)
                           | c <- toList $ getConstructorSymbols p
                           , let ar = getArity p c]
