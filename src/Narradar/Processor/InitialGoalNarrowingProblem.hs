{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns, RecordWildCards #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Narradar.Processor.InitialGoalNarrowingProblem where

import Control.Applicative
import Data.Foldable (Foldable, toList)
import Data.Traversable (Traversable)
import Data.List ((\\))
import Data.Monoid
import Data.Term
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Types
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.Problem.Infinitary
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGoal
import Narradar.Types.Problem.NarrowingGen as Gen
import Narradar.Utils


-- | This is the approach of Iborra, Nishida & Vidal
data NarrowingGoalToRelativeRewriting = NarrowingGoalToRelativeRewriting deriving (Eq, Show)
data NarrowingGoalToRelativeRewritingProof = NarrowingGoalToRelativeRewritingProof deriving (Eq, Show)

instance Pretty NarrowingGoalToRelativeRewritingProof where
  pPrint NarrowingGoalToRelativeRewritingProof = text "Relative Termination of the following relateive termination" $$
                                                 text "problem implies the termination of narrowing (LOPSTR'09)"


instance (gid ~ DPIdentifier (GenId id)
         ,Ord id, Pretty (GenId id)
         ,Traversable (Problem base), MkDPProblem base (NTRS gid), Pretty base
         ,NCap gid (base, NTRS gid)
         ,NUsableRules gid (base, NTRS gid, NTRS gid)
         ,HasSignature (NProblem base (DPIdentifier id)), DPIdentifier id ~ SignatureId (NProblem base (DPIdentifier id))
--         ,InsertDPairs (Relative (NTRS gid) (InitialGoal (TermF gid) (MkNarrowingGen base))) (NTRS gid)
         ,InsertDPairs base (NTRS gid)
         ,Info info NarrowingGoalToRelativeRewritingProof
         ) =>
         Processor info NarrowingGoalToRelativeRewriting
                        (NProblem (MkNarrowingGoal (DPIdentifier id) base) (DPIdentifier id))
                        (NProblem (Relative (NTRS gid) (InitialGoal (TermF gid)
                                                                    (MkNarrowingGen base)))
                                  gid)
  where
    apply NarrowingGoalToRelativeRewriting prob@NarrowingGoalProblem{goal=Goal goal_f modes, ..} =
            singleP NarrowingGoalToRelativeRewritingProof prob prob'
     where
{-
       prob'    = insertDPairs (mkDPProblem newType r' p')
                               (mkTRS [ l :-> r | l :-> r <- getPairs newType (goalRule:initialRules)
                                                , rootSymbol l == Just (IdDP GoalId)])
-}
       prob'    = mkDerivedProblem newType
                               (insertDPairs (mkDPProblem baseType r' p')
                                             (mkTRS [ l :-> r | l :-> r <- getPairs newType (goalRule:initialRules)
                                                              , rootSymbol l == Just (IdDP GoalId)]))

       baseType = getProblemType baseProblem
       newType  = relative genRules $ initialGoal [goal'] $ NarrowingGen baseType

       r'       = mapNarradarTRS convert (getR prob) `mappend` mkTRS [goalRule]
       p'       = mapNarradarTRS convert (getP prob)

       initialRules = [ rule | rule <- rules r'
                             , let Just id_f = getId (lhs rule)
                             , id_f == (AnId <$> unmarkDPSymbol goal_f)
                      ]

       goal'    = term (IdDP GoalId)       (return <$> toList goal_vars)
       goalRule = term (IdFunction GoalId) (return <$> toList goal_vars) :->
                  term (AnId <$> unmarkDPSymbol goal_f)
                       (take (length modes) [ if var `Set.member` goal_vars
                                               then return var
                                               else genTerm
                                             | var <- vars])

       genRules = tRS [ genTerm :-> term (AnId <$> c) (replicate ar genTerm)
                           | c <- toList $ getConstructorSymbols (getR prob)
                           , let ar = getArity prob c]

       genTerm   = term (IdFunction GenId) []
       goal_vars = Set.fromList [ v | (G,v) <- modes `zip` vars]
       vars = [toEnum 0 ..] \\ toList (getVars prob)
       convert  = mapTermSymbols (fmap AnId)


{-
instance ( HasId t, Foldable t, TermId t ~ id, SignatureId trs ~ id
         , Ord id, Ord (Term t Var), HasSignature trs
         ) =>
    Processor info NarrowingGoalToNarrowingGoal
              (Problem (InitialGoal t Narrowing) trs)
              (Problem (NarrowingGoal id) trs)
 where
  apply _ p = mprod [mkDerivedProblem (narrowingGoal g) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

instance ( HasId t, Foldable t, TermId t ~ id, Ord id, Ord (Term t Var)
         , HasSignature trs, SignatureId trs ~ id
         ) =>
    Processor info NarrowingGoalToNarrowingGoal
              (Problem (InitialGoal t CNarrowing) trs)
              (Problem (CNarrowingGoal id) trs)
 where
  apply _ p = mprod [mkDerivedProblem (cnarrowingGoal g) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p


instance ( HasId t, Foldable t, Ord (Term t Var), TermId t ~ id, Ord id
         , Info info (Problem (InitialGoal t Narrowing) trs)
         , HasSignature trs, SignatureId trs ~ id
         , Info info NarrowingGoalToInfinitaryRewritingProof
         ) =>
    Processor info NarrowingGoalToInfinitaryRewriting
              (Problem (InitialGoal t Narrowing) trs)
              (Problem (Infinitary id Rewriting) trs)
 where
  apply _ p = andP NarrowingGoalToInfinitaryRewritingProof p
                [mkDerivedProblem (infinitary g Rewriting) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p

instance ( HasId t, Foldable t, Ord (Term t Var), TermId t ~ id, Ord id
         , HasSignature trs, SignatureId trs ~ id
         , Info info NarrowingGoalToInfinitaryRewritingProof
         ) =>
    Processor info NarrowingGoalToInfinitaryRewriting
              (Problem (InitialGoal t CNarrowing) trs)
              (Problem (Infinitary id IRewriting) trs)
 where
  apply _ p = andP NarrowingGoalToInfinitaryRewritingProof p
              [mkDerivedProblem (infinitary g IRewriting) p | g <- gg]
    where InitialGoal gg _ _ = getProblemType p
-}
{-
instance (trsGDP ~ NarradarTRS gdp Var
         ,gid    ~ GenTermF id
         ,gdp    ~ GenTermF (DPIdentifier id)
         ,typ'   ~ InitialGoal gdp (Relative trsGDP NarrowingGen)
--         ,MkNarradarProblem (InitialGoal gdp (Relative trsGDP NarrowingGen)) gid
         ,Ord id
         ) =>
    Processor NarrowingGoalToRelativeRewriting
              (Problem (InitialGoal (TermF (DPIdentifier id)) Narrowing) (NTRS (DPIdentifier id) Var))
              (Problem (InitialGoal (GenTermF (DPIdentifier id))
                                      (Relative (NarradarTRS (GenTermF (DPIdentifier id)) Var) NarrowingGen))
                         (NarradarTRS (GenTermF (DPIdentifier id)) Var))
 where
   apply = initialGoalNarrowingToRelativeRewriting
-}

{-
initialGoalNarrowingToRelativeRewriting ::
              forall typ typ' tag id mp gid gdp trsG trsGDP info.
            ( gid  ~ GenTermF id
            , gdp  ~ GenTermF (DPIdentifier id)
            , typ  ~ InitialGoal (TermF (DPIdentifier id)) Narrowing
            , typ' ~ InitialGoal gdp (Relative trsGDP NarrowingGen)
            , trsG ~ NarradarTRS gid Var
            , trsGDP ~ NarradarTRS gdp Var
            , Ord id, Pretty (DPIdentifier id)
--            ,MkDPProblem (Relative trs NarrowingGen) trsGDP
            , Monad mp
            ) => tag -> Problem typ (NarradarTRS (TermF (DPIdentifier id)) Var)
                     -> Proof info mp (Problem typ' trsGDP)

initialGoalNarrowingToRelativeRewriting _ p =
              mprod [mkNewProblem (initialGoal [goal] (relative genRules narrowingGen))
                                  (tRS (goalRule : rr') :: trsG)
                      | Goal f modes <- gg
                      , let rr' = convert <$$> (rules $ getR p)
                      , let goal_vars =  [ v | (G,v) <- modes `zip` take (length modes) vars]
                      , let goalRule = goalTerm goal_vars :-> term (symbol f) (take (length modes) vars)
                    , let goal = Goal (GoalId :: GenId (DPIdentifier id)) []
                    ]
    where
      vars = map return ([toEnum 0 ..] \\ toList (getVars p))
      InitialGoal gg gr p0 = getProblemType p
      convert  = mapTerm (\(Narradar.Term id tt) -> Gen.Term (symbol id) tt)
      genRules = tRS [ genTerm :-> Gen.term c (replicate ar genTerm)
                           | c <- toList $ getConstructorSymbols p
                           , let ar = getArity p c]
-}
