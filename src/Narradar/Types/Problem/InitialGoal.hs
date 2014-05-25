{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{- LANGUAGE NoMonoLocalBinds -}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Narradar.Types.Problem.InitialGoal where

import Control.Applicative
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad.Free
import Control.Monad.List
import qualified Control.RMonad as R
import Control.RMonad.AsMonad (embed, unEmbed)
import Data.Bifunctor
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Array as A
import Data.Graph as G
import Data.Graph.SCC as SCC
import Data.Maybe
import Data.Monoid ( Monoid(..) )
import Data.Strict ( Pair(..) )
import Data.Suitable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Text.XHtml (HTML(..), theclass, (+++))

import Data.Term hiding ((!), TermF, Var)
import qualified Data.Term.Family as Family
import Data.Term.Rules

import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing hiding (baseProblem)
import Narradar.Types.Problem.NarrowingGen hiding (baseProblem, baseFramework)
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Var
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils

import qualified Narradar.Types.Problem.Narrowing as N

import Prelude hiding (pi)

data InitialGoal t p = InitialGoal
    { goals_PType     :: [CAGoal t]
    , dgraph_PType    :: Maybe (DGraph t Var)
    , baseFramework :: p}

data CAGoalF c a = Concrete c
                 | Abstract a
  deriving (Eq, Ord, Show, Functor)

type CAGoal t = CAGoalF (Term t Var) (Term t Mode)

instance (Eq p, Eq (Term t Var), Eq (Term t Mode)) => Eq (InitialGoal t p) where
    p0 == p1 = (goals_PType p0, baseFramework p0) == (goals_PType p1, baseFramework p1)

instance (Ord p, Ord (Term t Var), Ord (Term t Mode)) => Ord (InitialGoal t p) where
    compare p0 p1 = compare (goals_PType p0, baseFramework p0) (goals_PType p1, baseFramework p1)

instance (Show p, Show (Term t Var), Show (Term t Mode)) => Show (InitialGoal t p) where
    show p0 = show (goals_PType p0, baseFramework p0)

instance Functor (InitialGoal t) where
    fmap f (InitialGoal goals dg p) = InitialGoal goals dg (f p)

mapInitialGoal :: forall t t' p . (Functor t, Functor t', Foldable t', HasId t', Ord (Term t Var), Ord(Term t' Var)) =>
                  (forall a. t a -> t' a) -> InitialGoal t p -> InitialGoal t' p
mapInitialGoal f (InitialGoal goals dg p) = InitialGoal goals' dg' p
      where
        goals' = map (bimap f' f') goals
        dg'    = mapDGraph f' <$> dg
        f'    :: forall a. Term t a -> Term t' a
        f'     = foldTerm return (Impure . f)

instance (IsProblem p, HasId t, Foldable t) => IsProblem (InitialGoal t p) where
  data Problem (InitialGoal t p) a = InitialGoalProblem { goals       :: [CAGoal t]
                                                        , dgraph      :: DGraph t Var
                                                        , baseProblem :: Problem p a}
  getFramework (InitialGoalProblem goals g p) = InitialGoal goals (Just g) (getFramework p)
  getR   (InitialGoalProblem _     _ p) = getR p

instance (Eq (Problem p a)) => Eq (Problem (InitialGoal t p) a) where
  p1 == p2 = baseProblem p1 == baseProblem p2

instance (IsDPProblem p, HasId t, Foldable t) => IsDPProblem (InitialGoal t p) where
  getP   (InitialGoalProblem _     _ p) = getP p


instance ( t ~ f id, MapId f, DPSymbol id
         , MkDPProblem p (NarradarTRS t Var)
         , HasId t, Foldable t, Unify t
         , Ord (t(Term t Var)), Pretty (t(Term t Var))
         , Traversable (Problem p), Pretty p
         , ICap (p, NarradarTRS t Var)
         , IUsableRules p (NarradarTRS t Var)
         ) =>
     MkProblem (InitialGoal t p) (NarradarTRS t Var)
 where
  mkProblem (InitialGoal gg gr p) rr = initialGoalProblem gg gr (mkProblem p rr)
  mapR f (InitialGoalProblem goals dg p)
      = InitialGoalProblem goals dg' p'
   where
    p'     = mapR f p
    dg'    = mkDGraph' (getFramework p') (getR p') pairs' goals
    pairs' = dpTRS (getFramework p') (getR p') (pairs dg)


{-
instance (t ~ f id, MapId f, DPSymbol id
         ,HasId t, Unify t, Foldable t, Pretty p
         ,Pretty(t(Term t Var)), Ord (Term t Var), Traversable (Problem p)
         ,ICap t Var (p, NarradarTRS t Var)
         ,MkDPProblem p (NarradarTRS t Var)
         ,IUsableRules t Var p (NarradarTRS t Var)
         ) => MkDPProblem (InitialGoal t p) (NarradarTRS t Var) where
  mapP f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapP f p)
  mkDPProblem (InitialGoal goals g p) = (initialGoalProblem goals g .) . mkDPProblem p


 Necessary ugliness. Cannot give a generic MkDPProblem instance.
 The problem is that the call to mkDPProblem in the base framework
 computes and caches the unifiers of the problem.
 As this computation is done in the context of the base framework,
 then the goal directed usable rules are not employed, and we lose
 precision when computing the dependency graph, especially in absence
 of minimality.

 The current hack is to have monolitical MkDPProblem instances
 for every concrete framework: Initial goal rewriting, Initial goal
 innermost, Initial goal narrowing, etc.
 This hack has to be replicated also for other type classes, e.g.
 InsertDPair

 An alternative fix would be to disable the use of cached unifiers
 for initial goal problems, in the dependency graph (and refinement)
 processors, giving up performance.

 These are only patches around the problem. I'm afraid a proper fix
 calls for an encoding of inheritance to model the framework of a DP
 problem, which I don't have time to look at right now.
-}

instance (t ~ f id, MapId f, Unify t, DPSymbol id, HasId t
         ,Pretty (t(Term t Var)), Ord (t(Term t Var))) =>
    MkDPProblem (InitialGoal t Rewriting) (NarradarTRS t Var)
  where
  mkDPProblem (InitialGoal goals _ _) _ _
    | not $ all isVar (properSubterms =<< concrete goals)
      = error "Initial goals must be of the form f(x,y,z..)"
  mkDPProblem it@(InitialGoal goals g (MkRewriting s m)) rr dd
    = case dd of
        DPTRS{rulesUsed} | rr == rulesUsed
           -> initialGoalProblem goals g $
              RewritingProblem rr dd s m
        otherwise -> initialGoalProblem goals g $
                     RewritingProblem rr (dpTRS it rr dd) s m
  mapP f p@(InitialGoalProblem goals g (RewritingProblem rr pp s m))
    = InitialGoalProblem goals g' p'
   where
     p' :: Problem Rewriting (NarradarTRS t Var)
     p' = case f pp of
        pp'@DPTRS{rulesUsed}
            | rr == rulesUsed
            -> RewritingProblem rr pp' s m

        pp' -> RewritingProblem rr (dpTRS (getFramework p) rr pp') s m

     g' = mkDGraph' (getFramework p') (getR p) (pairs g) goals

instance (t ~ f id, MapId f, Unify t, DPSymbol id, HasId t
         ,Pretty (t(Term t Var)), Ord (t(Term t Var))) =>
    MkDPProblem (InitialGoal t IRewriting) (NarradarTRS t Var)
  where
  mkDPProblem it@(InitialGoal goals g (MkRewriting s m)) rr dd
    = case dd of
        DPTRS{rulesUsed} | rr == rulesUsed
           -> initialGoalProblem goals g $
              RewritingProblem rr dd s m
        otherwise -> initialGoalProblem goals g $
                     RewritingProblem rr (dpTRS it rr dd) s m
  mapP f p@(InitialGoalProblem goals g (RewritingProblem rr pp s m))
    = InitialGoalProblem goals g' p'
   where
     p' :: Problem IRewriting (NarradarTRS t Var)
     p' = case f pp of
        pp'@DPTRS{rulesUsed}
            | rr == rulesUsed
            -> RewritingProblem rr pp' s m

        pp' -> RewritingProblem rr (dpTRS (getFramework p) rr pp') s m

     g' = mkDGraph' (getFramework p') (getR p) (pairs g) goals



instance (t ~ f id, MapId f, Unify t, DPSymbol id, HasId t
         ,Pretty (t(Term t Var)), Ord (t(Term t Var))) =>
    MkDPProblem (InitialGoal t Narrowing) (NarradarTRS t Var)
  where
  mkDPProblem (InitialGoal goals _ _) _ _
    | not $ all isVar (properSubterms =<< concrete goals)
      = error "Initial goals must be of the form f(x,y,z..)"
  mkDPProblem it@(InitialGoal goals g (MkNarrowing (MkRewriting s m))) rr dd
    = case dd of
        DPTRS{rulesUsed} | rr == rulesUsed
           -> initialGoalProblem goals g $
              NarrowingProblem $
              RewritingProblem rr dd s m
        otherwise -> initialGoalProblem goals g $
                     NarrowingProblem $
                     RewritingProblem rr (dpTRS it rr dd) s m
  mapP f p@(InitialGoalProblem goals g (N.baseProblem -> RewritingProblem rr pp s m))
    = InitialGoalProblem goals g' p'
   where
     p' :: Problem Narrowing (NarradarTRS t Var)
     p' = case f pp of
        pp'@DPTRS{rulesUsed}
            | rr == rulesUsed
            -> NarrowingProblem $ RewritingProblem rr pp' s m

        pp' -> NarrowingProblem $ RewritingProblem rr (dpTRS (getFramework p) rr pp') s m

     g' = mkDGraph' (getFramework p') (getR p) (pairs g) goals



instance (t ~ f id, MapId f, Unify t, DPSymbol id, HasId t
         ,Pretty (t(Term t Var)), Ord (t(Term t Var))) =>
    MkDPProblem (InitialGoal t INarrowing) (NarradarTRS t Var)
  where
  mkDPProblem it@(InitialGoal goals g (MkNarrowing (MkRewriting s m))) rr dd
    = case dd of
        DPTRS{rulesUsed} | rr == rulesUsed
           -> initialGoalProblem goals g $
              NarrowingProblem $
              RewritingProblem rr dd s m
        otherwise -> initialGoalProblem goals g $
                     NarrowingProblem $
                     RewritingProblem rr (dpTRS it rr dd) s m
  mapP f p@(InitialGoalProblem goals g (N.baseProblem -> RewritingProblem rr pp s m))
    = InitialGoalProblem goals g' p'
   where
     p' :: Problem INarrowing (NarradarTRS t Var)
     p' = case f pp of
        pp'@DPTRS{rulesUsed}
            | rr == rulesUsed
            -> NarrowingProblem $ RewritingProblem rr pp' s m

        pp' -> NarrowingProblem $ RewritingProblem rr (dpTRS (getFramework p) rr pp') s m

     g' = mkDGraph' (getFramework p') (getR p) (pairs g) goals



instance (DPSymbol id, Pretty id, Ord id, GenSymbol id) =>
    MkDPProblem (InitialGoal (TermF id) NarrowingGen) (NTRS id)
  where
  mkDPProblem (InitialGoal goals _ _) _ _
    | not $ all isVar (properSubterms =<< concrete goals)
      = error "Initial goals must be of the form f(x,y,z..)"
  mkDPProblem typ@(InitialGoal goals g (NarrowingGen (MkRewriting s m))) rr dd
    = case dd of
        DPTRS{rulesUsed} | rr' == rulesUsed
           -> initialGoalProblem goals g $
              NarrowingGenProblem $
              RewritingProblem rr' dd' s m
        otherwise -> initialGoalProblem goals g' $
                     NarrowingGenProblem $
                     RewritingProblem rr' (dpTRS typ' rr' dd') s m
    where
      rr' = mapNarradarTRS' id extraVarsToGen rr
      dd' = mapNarradarTRS' id extraVarsToGen dd
      typ' = InitialGoal goals g' (NarrowingGen (MkRewriting s m))
      g'  = mapDGraph' id extraVarsToGen <$> g

  mapP f p@(InitialGoalProblem goals g (getBaseProblem -> RewritingProblem rr pp s m))
    = InitialGoalProblem goals g' p'
   where
     p' :: Problem NarrowingGen (NTRS id)
     p' = case f pp of
        pp'@DPTRS{rulesUsed}
            | rr == rulesUsed
            -> NarrowingGenProblem $ RewritingProblem rr pp' s m

        pp' -> NarrowingGenProblem $ RewritingProblem rr (dpTRS (getFramework p) rr pp') s m

     g' = mkDGraph' (getFramework p') (getR p) (pairs g) goals



instance (DPSymbol id, Pretty id, Ord id, GenSymbol id) =>
    MkDPProblem (InitialGoal (TermF id) INarrowingGen) (NTRS id)
  where
  mkDPProblem (InitialGoal goals _ _) _ _
    | not $ all isVar (properSubterms =<< concrete goals)
      = error "Initial goals must be of the form f(x,y,z..)"
  mkDPProblem it@(InitialGoal goals g (NarrowingGen (MkRewriting s m))) rr dd
    = case dd of
        DPTRS{rulesUsed} | rr' == rulesUsed
           -> initialGoalProblem goals g $
              NarrowingGenProblem $
              RewritingProblem rr' dd' s m
        otherwise -> initialGoalProblem goals g $
                     NarrowingGenProblem $
                     RewritingProblem rr' (dpTRS it rr' dd') s m
    where
      rr' = mapNarradarTRS' id extraVarsToGen rr
      dd' = mapNarradarTRS' id extraVarsToGen dd

  mapP f p@(InitialGoalProblem goals g (getBaseProblem -> RewritingProblem rr pp s m))
    = InitialGoalProblem goals g' p'
   where
     p' :: Problem INarrowingGen (NTRS id)
     p' = case f pp of
        pp'@DPTRS{rulesUsed}
            | rr == rulesUsed
            -> NarrowingGenProblem $ RewritingProblem rr pp' s m

        pp' -> NarrowingGenProblem $ RewritingProblem rr (dpTRS (getFramework p) rr pp') s m

     g' = mkDGraph' (getFramework p') (getR p) (pairs g) goals



instance FrameworkExtension (InitialGoal t) where
  getBaseFramework = baseFramework
  getBaseProblem   = baseProblem
  liftProblem   f p = f (baseProblem p) >>= \p0' -> return p{baseProblem = p0'}
  liftFramework f p = p{baseFramework = f $ baseFramework p}
  liftProcessorS = liftProcessorSdefault

initialGoal gg = InitialGoal gg Nothing

initialGoalProblem :: ( t ~ f id, MapId f, DPSymbol id
                      , HasId t, Unify t, Ord (Term t Var), Pretty (t(Term t Var))
                      , MkDPProblem typ (NarradarTRS t Var)
                      , Traversable (Problem typ), Pretty typ
                      , ICap (typ, NarradarTRS t Var)
                      , IUsableRules typ (NarradarTRS t Var)
                      ) =>
                      [CAGoal t]
                   -> Maybe(DGraph t Var)
                   -> Problem typ (NarradarTRS t Var) -> Problem (InitialGoal t typ) (NarradarTRS t Var)

initialGoalProblem gg Nothing p = InitialGoalProblem gg (mkDGraph p gg) p
initialGoalProblem gg (Just dg) p = InitialGoalProblem gg dg p

concrete gg = [g | Concrete g <- gg]
abstract gg = [g | Abstract g <- gg]
-- ----------
-- Functions
-- ----------
{-# RULES "Set fromList/toList" forall x. Set.fromList(Set.toList x) = x #-}

initialPairs :: Unify t => Problem (InitialGoal t base) trs -> [Rule t Var]
initialPairs InitialGoalProblem{..} = dinitialPairs dgraph


-- | returns the vertexes in the DGraph which are in a path from an initial pair to the current P
involvedNodes :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var)
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> [Vertex]
involvedNodes p = involvedNodes' (getFramework p) (getP p)

-- | returns the vertexes in the DGraph which are in a path from an initial pair to a given TRS P
involvedNodes' :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var), HasRules trs
                  ,Rule t Var ~ Family.Rule trs
                  ) => InitialGoal t base -> trs -> [Vertex]
involvedNodes' p@InitialGoal{dgraph_PType=Just dg@DGraph{..},..} pTRS
  = flattenSCCs (map (safeAt "involvedNodes" sccs) sccsInPath)
 where
   sccsInvolved = Set.fromList $ catMaybes $ [ sccFor n dg
                                                   | p <- rules pTRS
                                                   , Just n <- [lookupNode p dg]]
   initialSccs  = Set.fromList [ n | p0 <- toList initialPairsG
                                   , Just n <- [sccFor p0 dg]
                               ]

   sccsInPath   = toList $ unEmbed $ do
                    from <- embed initialSccs
                    to   <- embed sccsInvolved
                    embed $ nodesInPathNaive sccGraph from to

-- | Returns the pairs corresponding to the involved nodes in the DGraph
involvedPairs :: (t ~ f id, HasId t, MapId f, Foldable t, Unify t
                 ,IsDPProblem base, Traversable (Problem base)
                 ,Ord (Term t Var)
                 ,ICap (base, NarradarTRS t Var)
                 ,IUsableRules base (NarradarTRS t Var)
                 ,Pretty base, Pretty (Term t Var)
                 ,DPSymbol id
                  ) => InitialGoal t base -> NarradarTRS t Var -> NarradarTRS t Var -> [Rule t Var]
involvedPairs p@InitialGoal{dgraph_PType=Just dg@DGraph{..}} trs dps
  = map (`lookupPair` dg) (snub(involvedNodes' p dps ++ pairs ++ toList initialPairsG))
 where
   pairs = catMaybes(map (`lookupNode` dg) (rules dps))

involvedPairs p trs dps = rules dps

-- NOT POSSIBLE: mkDGraph' expects a DPTRS, whereas dpTRS calls involvedPairs
--involvedPairs p@InitialGoal{goals_PType} trs dps = involvedPairs p{dgraph_PType=Just dg} trs dps
--    where dg = mkDGraph' p trs dps goals_PType

reachableUsableRules :: (t ~ f id, Ord(Term t Var), HasId t, Foldable t, Unify t, MapId f
                        ,MkDPProblem base (NarradarTRS t Var), Traversable (Problem base)
                        ,ICap (base, NarradarTRS t Var)
                        ,IUsableRules base (NarradarTRS t Var)
                        ,NeededRules base (NarradarTRS t Var)
                        ,Pretty base, Pretty (Term t Var)
                        ,DPSymbol id
                        ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> NarradarTRS t Var

reachableUsableRules p = getR $ neededRules (getBaseProblem p) (rhs <$> forDPProblem involvedPairs p)

-- ---------
-- Instances
-- ---------

-- Functor

instance Functor (Problem p) => Functor (Problem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

instance Bifunctor CAGoalF where
  bimap fc fa (Concrete c) = Concrete (fc c)
  bimap fc fa (Abstract a) = Abstract (fa a)

-- Data.Term

-- NFData

instance (NFData (t(Term t Var)), NFData(Term t Mode), NFData (Family.Id t), NFData (Problem p trs)) =>
  NFData (Problem (InitialGoal t p) trs)
 where
  rnf (InitialGoalProblem gg g p) = rnf gg `seq` rnf g `seq` rnf p `seq` ()

instance (NFData a, NFData c) => NFData (CAGoalF c a) where
   rnf (Concrete g) = rnf g; rnf (Abstract g) = rnf g

-- Output

instance (Pretty (Term t Mode), Pretty (Term t Var)) => Pretty (CAGoal t) where
  pPrint (Concrete g) = text "concrete" <+> g
  pPrint (Abstract g) = text "abstract" <+> g

instance Pretty p => Pretty (InitialGoal id p) where
    pPrint InitialGoal{..} = text "Initial Goal" <+> pPrint baseFramework


instance (Pretty (Term t Var), Pretty(Term t Mode), Pretty (Problem base trs)) =>
    Pretty (Problem (InitialGoal t base) trs)
 where
  pPrint InitialGoalProblem{..} =
      pPrint baseProblem $$
      text "GOALS:" <+> pPrint goals


instance HTML p => HTML (InitialGoal id p) where
    toHtml InitialGoal{..} = toHtml "Initial goal " +++ baseFramework

instance HTMLClass (InitialGoal id typ) where htmlClass _ = theclass "G0DP"

instance (Pretty (Term t Var), Pretty (Term t Mode), PprTPDB (Problem typ trs)) =>
    PprTPDB (Problem (InitialGoal t typ) trs)
 where
    pprTPDB (InitialGoalProblem goals _ p) =
        pprTPDB p $$
        vcat [parens (text "STRATEGY GOAL" <+> g) | g <- goals]


-- ICap

instance (HasRules trs, Unify (Family.TermF trs), GetVars trs, ICap (p,trs)) =>
    ICap (InitialGoal id p, trs)
  where
    icap (InitialGoal{..},trs) = icap (baseFramework,trs)

-- Usable Rules

{-
instance (HasId t, Foldable t, Unify t, Ord (Term t Var), Pretty (Term t Var)
         ,IsDPProblem p, Traversable (Problem p), Pretty p
         ,trs ~ NarradarTRS t Var
         ,MkDPProblem p trs
         ,IUsableRules t Var (Problem p trs)
         ) =>
          IUsableRules t Var (Problem (InitialGoal t p) (NarradarTRS t Var))
  where
    iUsableRulesVar p = iUsableRulesVar (baseProblem p)
    iUsableRulesM p tt = do
      (getR -> reachableRules) <- iUsableRulesM (baseProblem p) (rhs <$> reachablePairs p)
      (getR -> trs')           <- iUsableRulesM (setR reachableRules (baseProblem p)) tt
      return (setR trs' p)
-}
instance (t ~ f id, MapId f, HasId t, Foldable t, Unify t
         ,Ord (t(Term t Var)), Pretty (t(Term t Var))
         ,IsDPProblem p, Traversable (Problem p), Pretty p
         ,DPSymbol id
         ,trs ~ NarradarTRS t Var
         ,ICap (p, trs)
         ,IUsableRules p trs
         ,NeededRules p trs
         ) =>
          IUsableRules (InitialGoal (f id) p) trs
  where
    iUsableRulesVarM it@(InitialGoal _ _ typ) trs dps v = do
      reachableRules <- neededRulesM typ trs dps (rhs <$> involvedPairs it trs dps)
      iUsableRulesVarM typ reachableRules dps v

    iUsableRulesM it@(InitialGoal _ _ typ) trs dps tt = do
      reachableRules <- neededRulesM typ trs dps =<< getFresh (rhs <$> involvedPairs it trs dps)
      pprTrace( text "The reachable rules are:" <+> pPrint reachableRules) (return ())
      iUsableRulesM typ reachableRules dps tt


-- Other Narradar instances

instance (trs ~ NTRS id
         ,MkDPProblem (InitialGoal (TermF id) typ) trs
         ,Pretty typ, Traversable (Problem typ)
         ,Pretty id, Ord id, DPSymbol id
         ,NNeededRules typ id
         ,NUsableRules typ id
         ,NCap typ id
         ,InsertDPairs typ (NTRS id)
         ) =>
  InsertDPairs (InitialGoal (TermF id) typ) (NTRS id)
 where
  insertDPairs p@InitialGoalProblem{dgraph=DGraph{..},..} newPairs
    = let dgraph' = insertDGraph p newPairs
      in insertDPairsDefault (initialGoalProblem goals (Just dgraph') baseProblem) newPairs

-- -------------------------------
-- Dependency Graph data structure
-- -------------------------------
type DGraph t v = DGraphF (Term t v)

-- Invariant - the pairs field is always a DPTRS

data DGraphF a = DGraph {pairs    :: NarradarTRSF (RuleF a)    -- ^ A DPTRS storing all the pairs in the problem and the depGraph
                        ,pairsMap :: Map (RuleF a) Vertex      -- ^ Mapping from pairs to vertexes in the sccs graph
                        ,initialPairsG   :: Set Vertex         -- ^ Set of vertexes corresponding to initial pairs
                        ,reachablePairsG :: Set Vertex         -- ^ Set of vertexes corresponding to reachable pairs
                        ,sccs     :: Array Int (SCC Vertex)    -- ^ Array of SCCs in the dep graph
                        ,sccsMap  :: Array Vertex (Maybe Int)  -- ^ Mapping from each vertex to its SCC
                        ,sccGraph :: Graph}                    -- ^ Graph of the reachable SCCs in the dep graph

fullgraph :: DGraph t v -> Graph
fullgraph = rulesGraph . pairs

deriving instance Show a => Show (SCC a)
instance Pretty (Term t v) => Pretty (DGraph t v) where
  pPrint DGraph{..} = text "DGraphF" <> brackets(vcat [text "pairs =" <+> pPrint (elems $ rulesArray pairs)
                                                      ,text "pairsMap =" <+> pPrint pairsMap
                                                      ,text "initial pairs = " <+> pPrint initialPairsG
                                                      ,text "reachable pairs = " <+> pPrint reachablePairsG
                                                      ,text "graph =" <+> text (show $ rulesGraph pairs)
                                                      ,text "sccs =" <+> text (show sccs)
                                                      ,text "sccsMap =" <+> pPrint (elems sccsMap)
                                                      ,text "sccGraph =" <+> text (show sccGraph)])

instance (NFData (t(Term t v)), NFData (Family.Id t), NFData v) => NFData (DGraph t v) where
  rnf (DGraph p pm ip rp sccs sccsm sccg)  = rnf p  `seq`
                                             rnf pm `seq`
                                             rnf ip `seq`
                                             rnf rp `seq`
--                                             rnf sccs `seq`
                                             rnf sccsm `seq`
                                             rnf sccg


mapDGraph :: (Ord(Term t v), Ord(Term t' v), Foldable t', HasId t') => (Term t v -> Term t' v) -> DGraph t v -> DGraph t' v
mapDGraph f (DGraph p pm ip rp sccs sccsM sccsG)
    = (DGraph (mapNarradarTRS f p) (Map.mapKeys (fmap f) pm) ip rp sccs sccsM sccsG)

mapDGraph' :: (Ord(Term t v), Ord(Term t' v), Foldable t', HasId t')
           => (Term t v -> Term t' v)
           -> (Rule t v -> Rule t' v)
           -> DGraph t v -> DGraph t' v
mapDGraph' ft fr (DGraph p pm ip rp sccs sccsM sccsG)
    = (DGraph (mapNarradarTRS' ft fr p) (Map.mapKeys fr pm) ip rp sccs sccsM sccsG)


mkDGraph :: ( t ~ f id, MapId f, DPSymbol id
            , v ~ Var
            , MkDPProblem typ (NarradarTRS t v)
            , Traversable (Problem typ), Pretty typ
            , HasId t, Unify t
            , Pretty (Term t v)
            , Ord    (Term t v)
            , ICap (typ, NarradarTRS t v)
            , IUsableRules typ (NarradarTRS t v)
            ) => Problem typ (NarradarTRS t v) -> [CAGoal t] -> DGraph t v
--mkDGraph (getP -> dps) _ | pprTrace ("mkDGraph with pairs: "<> dps) False = undefined
mkDGraph p@(getP -> DPTRS _ _ gr _ _) gg = mkDGraph' (getFramework p) (getR p) (getP p) gg

mkDGraph' :: ( t ~ f id, DPSymbol id, MapId f
             , v ~ Var
             , IsDPProblem typ, Traversable (Problem typ), Pretty typ
             , HasId t, Unify t, Pretty (Term t v)
             , ICap (typ, NarradarTRS t v)
             ) => typ -> NarradarTRS t v -> NarradarTRS t v -> [CAGoal t] -> DGraph t v
mkDGraph' typ trs pairs@(DPTRS dpsA _ fullgraph _ _) goals = runIcap (rules trs ++ rules pairs) $ do
  let pairsMap = Map.fromList (map swap $ assocs dpsA)
      p   = (typ,trs)

  -- List of indexes for fullgraph
  initialPairsG <- liftM Set.fromList $ runListT $ do
                     (i,s :-> t) <- liftL (assocs dpsA)
                     g           <- liftL goals
                     case g of
                       Concrete g -> do g' <- lift (getFresh g >>= icap p)
                                        guard(markDP g' `unifies` s)
                                        return i
                       Abstract g -> do guard (rootSymbol g == rootSymbol s)
                                        return i

  let -- list of indexes for fullgraph
      reachablePairsG = Set.fromList $ concatMap (reachable fullgraph) (toList initialPairsG)

      -- A list of tuples (ix, scc, edges)
      sccGraphNodes = [ it | it@(flattenSCC -> nn,_,_) <-SCC.sccGraph fullgraph
                           , any (`Set.member` reachablePairsG) nn]

      sccsIx   = [ ix | (_,ix,_) <- sccGraphNodes]
      sccGraph  = case sccsIx of
                    [] -> emptyArray
                    _  -> buildG (minimum sccsIx, maximum sccsIx)
                         [ (n1,n2) | (_, n1, nn) <- sccGraphNodes
                                   , n2 <- nn]
      sccs      = case sccsIx of
                    [] -> emptyArray
                    _  -> array (minimum sccsIx, maximum sccsIx)
                                 [ (ix, scc) | (scc,ix,_) <- sccGraphNodes]

      -- The scc for every node, with indexes from fullgraph
      sccsMap    = array (bounds fullgraph) (zip (indices dpsA) (repeat Nothing) ++
                                         [ (n, Just ix) | (scc,ix,_) <- sccGraphNodes
                                                                   , n <- flattenSCC scc])
      the_dgraph = DGraph {..}


--  pprTrace (text "Computing the dgraph for problem" <+> pPrint (typ, trs, pairs) $$
--            text "The initial pairs are:" <+> pPrint initialPairsG $$
--            text "where the EDG is:" <+> text (show fullgraph)
--            text "The final graph stored is:" <+> text (show graph) $$
--            text "where the mapping used for the nodes is" <+> pPrint (assocs reindexMap) $$
--            text "and the final initial pairs are:" <+> pPrint initialPairsG
--           ) $

  -- The index stored for a pair is within the range of the pairs array
--   assert (all (inRange (bounds pairs)) (Map.elems pairsMap)) $
  -- The scc index stored for a pair is within the range of the sccs array
  assert (all (maybe True (inRange (bounds sccs))) (elems sccsMap)) $
  -- No duplicate edges in the graph
   assert (noDuplicateEdges fullgraph) $
  -- There must be at least one initial pair, right ?
   return the_dgraph

  where
    liftL :: Monad m => [a] -> ListT m a
    liftL = ListT . return

insertDGraph p@InitialGoalProblem{..} newdps
    = mkDGraph' (getFramework p') (getR p') dps' goals
  where
    p'     =  insertDPairs (setP (pairs dgraph) p) newdps
    dps'   = getP p'

expandDGraph ::
      ( t ~ f id
      , Unify t, HasId t, MapId f, DPSymbol id
      , Ord (t(Term t Var)), Pretty (t(Term t Var))
      , Traversable (Problem typ)
      , IsDPProblem typ, Pretty typ
      , MkDPProblem (InitialGoal t typ) (NarradarTRS t Var)
      , ICap (typ, NarradarTRS t Var)
      , IUsableRules typ (NarradarTRS t Var)
      , NeededRules typ (NarradarTRS t Var)
      ) =>
       Problem (InitialGoal t typ) (NarradarTRS t Var)
    -> Rule t Var
    -> [Rule t Var]
    -> Problem (InitialGoal t typ) (NarradarTRS t Var)
expandDGraph p@InitialGoalProblem{dgraph=dg@DGraph{..},goals} olddp newdps
   = case lookupNode olddp dg of
      Nothing -> p
      Just i  -> p{dgraph=expandDGraph' p i newdps}

expandDGraph' ::
      ( t ~ f id
      , Unify t, HasId t, MapId f, DPSymbol id
      , Ord (t(Term t Var)), Pretty (t(Term t Var))
      , Traversable (Problem typ)
      , IsDPProblem typ, Pretty typ
      , MkDPProblem (InitialGoal t typ) (NarradarTRS t Var)
      , ICap (typ, NarradarTRS t Var)
      , IUsableRules typ (NarradarTRS t Var)
      , NeededRules typ (NarradarTRS t Var)
      ) =>
       Problem (InitialGoal t typ) (NarradarTRS t Var)
    -> Int
    -> [Rule t Var]
    -> DGraph t Var
expandDGraph' p@InitialGoalProblem{dgraph=dg@DGraph{..},goals} i newdps
   = mkDGraph (expandDPair (setP pairs p) i newdps) goals

data instance Constraints DGraphF a = Ord a => DGraphConstraints
instance Ord a => Suitable DGraphF a where
  constraints = DGraphConstraints

lookupNode p dg = Map.lookup p (pairsMap dg)

lookupPair n dg = safeAt "lookupPair" (rulesArray $ pairs dg) n

sccFor n dg = safeAt "sccFor" (sccsMap dg) n

dreachablePairs DGraph{..} = Set.fromList $ rules pairs

dinitialPairs g = map (safeAt "initialPairs" (rulesArray $ pairs g)) (toList $ initialPairsG g)


nodesInPath :: DGraphF a -> Vertex -> Vertex -> Set Vertex
-- TODO Implement as a BF traversal on the graph, modified to accumulate the
--      set of possible predecessors instead of the direct one
nodesInPath dg@DGraph{..} from to
    | Just from' <- sccFor from dg
    , Just to'   <- sccFor to   dg
    , sccsInPath <- Set.intersection (Set.fromList $ reachable sccGraph from')
                                     (Set.fromList $ reachable (transposeG sccGraph) to')
    = Set.fromList (flattenSCCs [safeAt "nodesInPath" sccs i | i <- Set.toList sccsInPath])

    | otherwise = Set.empty


nodesInPathNaive g from to = Set.intersection (Set.fromList $ reachable g from)
                                              (Set.fromList $ reachable g' to)
  where g' = transposeG g
