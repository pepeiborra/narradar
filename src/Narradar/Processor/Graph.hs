{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, DisambiguateRecordFields, ViewPatterns #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}

module Narradar.Processor.Graph
 ( dependencyGraphSCC
 , dependencyGraphCycles
 , DependencyGraph(..)
 , DependencyGraphProof(..)
 ) where

import Control.Applicative
import Control.Monad
import Control.Exception (assert)
import Control.DeepSeq
import Data.Array as A
import Data.Foldable (Foldable, foldMap, toList)
import Data.Functor.Two
import Data.Graph as G
import Data.Graph.SCC as GSCC
import qualified Data.Graph.Inductive as FGL
import Data.List (find, sort)
import Data.Strict.Tuple (Pair(..))
import Data.Traversable (Traversable)
import Data.Tree  as Tree
import Data.Typeable
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Prelude hiding (pi)
import Text.XHtml (HTML(..))

import Narradar.Framework
import Narradar.Framework.GraphViz

import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types hiding ((!))
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.QRewriting
import Narradar.Utils hiding (O)
import Narradar.Framework.Ppr

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe as Hood

-- -------------------------------------
-- DP Processors estimating the graph
-- -------------------------------------

data DependencyGraph (info :: * -> *) = DependencyGraphSCC {useInverse::Bool}
                                      | DependencyGraphCycles {useInverse::Bool}
        deriving (Eq, Ord, Show, Generic)

type instance InfoConstraint (DependencyGraph info) = info

instance Observable1 info => Observable (DependencyGraph info)

dependencyGraphSCC = DependencyGraphSCC True
dependencyGraphCycles = DependencyGraphCycles True

-- Implements Theorem 3.4 of Rene's thesis
instance ( Info info (NarradarProblem typ t)
         , FrameworkN typ t Var
         , Info info DependencyGraphProof
         ) =>
    Processor (DependencyGraph info) (Problem typ (NarradarTRS t Var)) where
  type Typ (DependencyGraph info) (Problem typ (NarradarTRS t Var)) = typ
  type Trs (DependencyGraph info) (Problem typ (NarradarTRS t Var)) = NarradarTRS t Var
  applyO _ (DependencyGraphSCC useInverse) = sccProcessor useInverse
  applyO _ (DependencyGraphCycles useInverse) = cycleProcessor useInverse


instance ( FrameworkId id
         , Info info DependencyGraphProof
         , Pretty (SomeInfo info)
         ) =>
    Processor (DependencyGraph info) (Problem (QRewritingN id) (NarradarTRS (TermF id) Var)) where
  type Typ (DependencyGraph info) (Problem (QRewritingN id) (NTRS id)) = QRewritingN id
  type Trs (DependencyGraph info) (Problem (QRewritingN id) (NTRS id)) = NTRS id
  applyO (O o oo) (DependencyGraphSCC useInverse) problem@(QRewritingProblem rr dps@(lowerNTRS -> DPTRS _ dd _ gr unifs sig) q m qC) =
             let graph = o "graph" $  (if useInverse then getIEDGfromUnifiers else oo "getEDG" getEDGfromUnifiersO) (o "unif'" unif')
                 unif' =  fmap filterNonQNF unifs
                 cc  = o "cc" [vv | CyclicSCC vv <- o "sccList" GSCC.sccList graph]

                 inQNF_ = o "inQNF" inQNF

                 filterNonQNF = imap (\ (x,y) -> ensure(\(Two sigma1 sigma2) ->
                                     --pprTrace sigma2 $
                                     (applySubst (sigma1) (lhs(dd ! x)) `inQNF_` q)
                                   &&
                                      applySubst (sigma2) (lhs(dd ! y)) `inQNF_` q
                                     ))

                 imap f a = listArray (bounds a) (map (uncurry f) (assocs a)) `asTypeOf` a

                 ensure p m = do
                    x <- m
                    when (not$ p x) $ pprTrace (text "Dropping unifier" <+> pPrint x) $ return ()
                    guard (p x)
                    return x
             in if null cc then success (NoCycles graph) problem else

-- The case below removes 'identity' applications of this processor from the proof log
-- Generally you want to do this for clarity, but there is one exception.
-- In the first step of a termination proof this processor is always applied, and you want to show it in the proof log.
-- However the case below will prevent that from happening,
-- in cases where there is one big scc that includes all the pairs in the problem
--  | [c] <- cc, sort c == sort (vertices graph) = return problem

                 andP (SCCs graph (map Set.fromList cc)) problem
                     -- we don't call setP below to avoid recalculating the dps unifiers
                   [ QRewritingProblem rr dps' q m qC
                     | ciclo <- cc
                     , let dps' = oo "restrict" restrictTRSO dps ciclo]


instance ( t ~ f (DPIdentifier id0), MapId f
         , Family.Id t ~ DPIdentifier id0, Ord id0
         , trs ~ NarradarTRS t Var
         , problem ~ Problem (InitialGoal t typ0) trs, Info info problem
         , FrameworkN typ0 t Var
         , FrameworkN (InitialGoal t typ0) t Var
         , Info info DependencyGraphProof
         ) =>
    Processor (DependencyGraph info) (Problem (InitialGoal t typ0) (NarradarTRS t Var))
 where
  type Typ (DependencyGraph info) (Problem (InitialGoal t typ0) (NarradarTRS t Var)) = InitialGoal t typ0
  type Trs (DependencyGraph info) (Problem (InitialGoal t typ0) (NarradarTRS t Var)) = NarradarTRS t Var
  applyO _ DependencyGraphCycles{} _ = error "Cycles processor not available for Initial Goal problems"
  applyO _ (DependencyGraphSCC useInverse)
        p@InitialGoalProblem{ dgraph=dg@DGraph{pairs, initialPairsG, reachablePairsG}
                            , baseProblem = (getP -> dps@(lowerNTRS -> DPTRS _ dd _ igr unif sig))}
   = do
    let gr            = if useInverse then igr else getEDGfromUnifiers unif
        reachable     = Set.fromList [ i | (i,dp) <- assocs dd, isReachable dp]
        isReachable p =  fromMaybe False (flip Set.member reachablePairsG <$> lookupNode p dg)

        grForSccs   = buildG (bounds gr)
                       [ (i,o) | (i,o) <- edges gr
                               , i `Set.member` reachable
                               , o `Set.member` reachable]

        cc   = [vv | CyclicSCC vv <- GSCC.sccList grForSccs]

        proof = UsableSCCs{ gr         = fullgraph dg
                          , initial    = initialPairsG
                          , outOfScope = Set.fromList(vertices $ fullgraph dg) `Set.difference` reachablePairsG
                          , inPath     = Set.fromList $ involvedNodes' (getFramework p) (map (safeAt "DependencyGraphSCC" dd) (concat cc))
                          , the_pairs  = rules pairs
                          , the_sccs   = map Set.fromList cc }

        proof2= NoUsableSCCs{ gr         = fullgraph dg
                            , initial    = initialPairsG
                            , outOfScope = Set.fromList(vertices $ fullgraph dg) `Set.difference` reachablePairsG
                            , inPath     = Set.fromList $ involvedNodes' (getFramework p) (map (safeAt "DependencyGraphSCC" dd) (concat cc))
                            , the_pairs  = rules pairs
                            }

    case cc of
     [] -> if null (rules dps) then success (NoCycles gr) p else success proof2 p
     [c] | sort c == sort(vertices gr) -> return p
     cc -> andP proof p
               [setP (restrictTRS dps scc) p | scc <- cc]

-- --------------
-- Graph Proofs
-- --------------

data DependencyGraphProof = SCCs   Graph [Set Vertex]
                          | forall a. Pretty a =>
                            UsableSCCs { gr :: Graph
                                       , initial, outOfScope, inPath :: Set Vertex
                                       , the_sccs  :: [Set Vertex]
                                       , the_pairs :: [a]}
                          | Cycles Graph
                          | NoCycles Graph
                          | forall a. Pretty a =>
                            NoUsableSCCs { gr :: Graph
                                         , initial, outOfScope, inPath :: Set Vertex
                                         , the_pairs :: [a]}

  deriving (Typeable)

instance Eq  DependencyGraphProof where a == b = pPrint a == pPrint b
instance Ord DependencyGraphProof where compare a b = compare (pPrint a) (pPrint b)
instance Observable DependencyGraphProof where
  observer = observeOpaque "DependencyGraphProof"

instance Pretty DependencyGraphProof where
  pPrint UsableSCCs{} = text "Dependency Graph Processor (SCCs)"
  pPrint SCCs{}   = text "Dependency Graph Processor (SCCs)"
  pPrint Cycles{} = text "Dependency Graph Processor (cycles)"
  pPrint NoCycles{} = text "We need to prove termination for all the cycles." <+>
                      text "There are no cycles, so the system is terminating"
  pPrint NoUsableSCCs{} = text "We need to prove termination for all the cycles." <+>
                          text "There are no cycles, so the system is terminating"

instance HTML DependencyGraphProof where toHtml = toHtml . show . pPrint

instance DotRep DependencyGraphProof where
  dot (NoCycles g) | null (G.vertices g) = Text (text "There are no cycles, the problem is finite.") []
  dot (NoCycles g) = let nn    = G.vertices g
                         nodes = FGL.mkGraph [(n, [label(int n)]) | n <- nn]
                                             [(a,b,[]) | (a,b) <- G.edges g]
                     in Nodes{nodes,attributes=[],incoming=head nn, outgoing=head nn, legend=Nothing}

  dot (Cycles g) = let n     = head (G.vertices g)
                       graph = FGL.mkGraph nodes edges
                       nodes = [(n, [label (int n)]) | n <- G.vertices g]
                       edges = [(a,b,[]) | (a,b) <- G.edges g]
                   in  Nodes {nodes=graph, attributes=[], incoming=n, outgoing=n, legend=Nothing}

  dot (SCCs g sccs) = Nodes {nodes      = coloredGraph
                            ,attributes = []
                            ,incoming   = fst $ head coloredNodes
                            ,outgoing   = fst $ head coloredNodes
                            ,legend     = Nothing}
     where
   coloredGraph = FGL.mkGraph coloredNodes coloredEdges
   coloredNodes = [ case safeAt "DependencyGraphProof.DotRep.coloredNodes" nodeColorsA n of
                        Nothing -> (n,[label (int n)])
                        Just c  -> (n, [label (int n), LabelFontColor (head c), Color c])
                      | n <- G.vertices g]
   nodeColorsA  = A.listArray (A.bounds g) [ snd <$> find ((n `Set.member`) . Prelude.fst) (zip sccs colors)
                                             | n <- G.vertices g]
   coloredEdges = [ (a,b,att)
                       | (a,b) <- G.edges g
                       , let att = case (safeAt "DependencyGraphProof.DotRep.coloredEdges" nodeColorsA a
                                        ,safeAt "DependencyGraphProof.DotRep.coloredEdges" nodeColorsA b) of
                                     (Just c1, Just c2) | c1 == c2 -> [Color c1]
                                     otherwise          -> []
                  ]

-- TODO Improve the usable SCCs graphviz output
  dot UsableSCCs{..} = Nodes {nodes      = coloredGraph
                             ,attributes = []
                             ,incoming   = fst $ head coloredNodes
                             ,outgoing   = fst $ head coloredNodes
                             ,legend     = Just (vcat [ n <+> text "-" <+> p
                                                        | (n,p) <- zip [0::Int ..] the_pairs]
                                                ,[FontName "monospace"
                                                 ,FontSize 9])
                             }
     where
   coloredGraph = FGL.mkGraph coloredNodes coloredEdges
   sccNodes     = Set.unions the_sccs
   coloredNodes = [ case True of
                      _ | n `Set.member` initial ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "red"), Color $ mkColor "red"])
                        | n `Set.member` sccNodes ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "green"), Color $ mkColor "yellow"])
                        | n `Set.member` inPath ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "rosybrown1"), Color $ mkColor "rosybrown1"])
                        | n `Set.member` outOfScope ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "gray"), Color $ mkColor "gray"])
                        | otherwise -> (n,[label (int n)])
                      | n <- G.vertices gr]
   coloredEdges = [ (a,b, case True of
                            _ | a `Set.member` sccNodes && b `Set.member` sccNodes ->
                                 [Color $ mkColor "yellow"]
                              | a `Set.member` inPath && b `Set.member` inPath ->
                                 [Color $ mkColor "rosybrown1"]
                              | a `Set.member` outOfScope || b `Set.member` outOfScope ->
                                 [Color $ mkColor "gray"]
                              | otherwise -> [])
                    | (a,b) <- G.edges gr]


  dot NoUsableSCCs{..} = Nodes {nodes      = coloredGraph
                               ,attributes = []
                               ,incoming   = fst $ head coloredNodes
                               ,outgoing   = fst $ head coloredNodes
                               ,legend     = Just (vcat [ n <+> text "-" <+> p
                                                        | (n,p) <- zip [0::Int ..] the_pairs]
                                                   ,[FontName "monospace"
                                                   ,FontSize 9])
                               }
     where
   coloredGraph = FGL.mkGraph coloredNodes coloredEdges
   coloredNodes = [ case True of
                      _ | n `Set.member` initial ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "red"), Color $ mkColor "red"])
                        | n `Set.member` inPath ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "rosybrown1"), Color $ mkColor "rosybrown1"])
                        | n `Set.member` outOfScope ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "gray"), Color $ mkColor "gray"])
                        | otherwise -> (n,[label (int n)])
                      | n <- G.vertices gr]
   coloredEdges = [ (a,b, case True of
                            _ | a `Set.member` inPath && b `Set.member` inPath ->
                                 [Color $ mkColor "rosybrown1"]
                              | a `Set.member` outOfScope || b `Set.member` outOfScope ->
                                 [Color $ mkColor "gray"]
                              | otherwise -> [])
                    | (a,b) <- G.edges gr]


colors = cycle $ map mkColor ["darkorange", "hotpink", "hotpink4", "purple", "brown","red","green","yellow"]

-- ---------------
-- Implementation
-- ---------------
type GraphProcessor typ t mp =   (Info info (NarradarProblem typ t)
                                 ,FrameworkProblem typ (NarradarTRS t Var)
                                 ,Info info DependencyGraphProof
                                 ,Monad mp
                                 ) => Bool ->
                                    NarradarProblem typ t -> Proof info mp (NarradarProblem typ t)

cycleProcessor, sccProcessor :: GraphProcessor typ t mp

sccProcessor useInverse problem@(getP -> dps@(lowerNTRS -> DPTRS _ dd _ gr unif sig))
  | null cc   = success (NoCycles graph) problem

-- The case below removes 'identity' applications of this processor from the proof log
-- Generally you want to do this for clarity, but there is one exception.
-- In the first step of a termination proof this processor is always applied, and you want to show it in the proof log.
-- However the case below will prevent that from happening,
-- in cases where there is one big scc that includes all the pairs in the problem
--  | [c] <- cc, sort c == sort (vertices graph) = return problem

  | otherwise = andP (SCCs graph (map Set.fromList cc)) problem
                 [setP (restrictTRS dps ciclo) problem | ciclo <- cc]
    where
      graph = if useInverse then gr else getEDGfromUnifiers unif
      cc  = [vv | CyclicSCC vv <- GSCC.sccList graph]

cycleProcessor useInverse problem@(getP -> dps@(lowerNTRS -> DPTRS _ dd _ gr unif sig))
  | null cc   = success (NoCycles graph) problem
  | [c] <- cc, sort c == sort (vertices graph) = return problem
  | otherwise = andP (Cycles graph) problem
                 [setP (restrictTRS dps ciclo) problem | ciclo <- cc]
    where
      graph = if useInverse then gr else getEDGfromUnifiers unif
      cc = cycles graph


