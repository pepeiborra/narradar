{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, DisambiguateRecordFields, ViewPatterns #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Narradar.Processor.Graph where

import Control.Applicative
import Control.Exception (assert)
import Data.Array as A
import Data.Graph as G
import Data.Graph.SCC as GSCC
import qualified Data.Graph.Inductive as FGL
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (find)
import Data.Traversable (Traversable)
import Data.Tree  as Tree
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
import Narradar.Utils
import Narradar.Framework.Ppr

-- -------------------------------------
-- DP Processors estimating the graph
-- -------------------------------------

data DependencyGraphSCC    = DependencyGraphSCC    deriving (Eq, Ord, Show)
data DependencyGraphCycles = DependencyGraphCycles deriving (Eq, Ord, Show)


instance ( trs ~ NarradarTRS t Var
         , problem ~ Problem typ trs, Info info problem
         , MkDPProblem typ (NarradarTRS t Var), Traversable (Problem typ)
         , Unify t, ICap t Var (typ,trs)
         , Pretty (Term t Var), Pretty typ
         , Info info DependencyGraphProof
         ) =>
    Processor info DependencyGraphSCC (Problem typ (NarradarTRS t Var)) (Problem typ (NarradarTRS t Var)) where
  apply DependencyGraphSCC = sccProcessor


instance ( TermId t ~ DPIdentifier id0, Ord id0
         , trs ~ NarradarTRS t Var
         , problem ~ Problem (InitialGoal t typ0) trs, Info info problem
         , MkDPProblem typ0 (NarradarTRS t Var), Traversable (Problem typ0)
         , HasId t, Unify t, Ord (Term t Var)
         , Pretty (t(Term t Var)), Pretty typ0
         , ICap t Var (typ0,trs)
         , IUsableRules t Var (typ0,trs,trs)
         , ProblemColor problem, PprTPDBDot problem
         , Info info DependencyGraphProof
         ) =>
    Processor info DependencyGraphSCC
             (Problem (InitialGoal t typ0) (NarradarTRS t Var))
             (Problem (InitialGoal t typ0) (NarradarTRS t Var))
 where
  apply DependencyGraphSCC p@InitialGoalProblem{ dgraph=dg@DGraph{..}
                                               , baseProblem = (getP -> dps@(DPTRS dd gr unif sig))}
   = do
    let reach_nodes = Set.fromList (fst <$> filter (isReachable.snd) (assocs dd))
        isReachable = isJust . (`lookupNode` dg)

        grForSccs   = buildG (bounds gr)
                       [ (i,o) | (i,o) <- edges gr
                               , i `Set.member` reach_nodes
                               , o `Set.member` reach_nodes]


        cc   = [vv | CyclicSCC vv <- GSCC.sccList grForSccs]

        initial_nodes = Set.fromList $ catMaybes [Map.lookup dp pairsMap | dp <- initialPairs p]
        reach_nodes_ix = Set.fromList [ ix | dp <- toList dd, Just ix <- [lookupNode dp dg]]
        usable_rules_ix= reachableNodes p
        out_nodes_ix   = Set.fromList (vertices graph) `Set.difference` reach_nodes_ix
        pairsMap = Map.fromList [ (n,dp) | (dp,n) <- A.assocs dd]

        proof = UsableSCCs{ gr         = graph
                          , reachable  = reach_nodes_ix
                          , initial    = Set.fromList initialPairsG
                          , outOfScope = out_nodes_ix
                          , inPath     = Set.fromList (reachableNodes p)
                          , the_pairs  = elems pairs}

    if null cc
     then success NoCycles p
     else andP proof p
               [setP (restrictDPTRS (DPTRS dd gr unif sig) ciclo) p | ciclo <- cc]

-- --------------
-- Graph Proofs
-- --------------

data DependencyGraphProof = SCCs   Graph [Set Vertex]
                          | forall a. Pretty a =>
                            UsableSCCs { gr :: Graph
                                       , reachable, initial, outOfScope, inPath :: Set Vertex
                                       , the_pairs :: [a]}
                          | Cycles Graph
                          | NoCycles

instance Pretty DependencyGraphProof where
  pPrint UsableSCCs{} = text "Dependency Graph Processor (SCCs)"
  pPrint SCCs{}   = text "Dependency Graph Processor (SCCs)"
  pPrint Cycles{} = text "Dependency Graph Processor (cycles)"
  pPrint NoCycles = text "We need to prove termination for all the cycles." <+>
                 text "There are no cycles, so the system is terminating"

instance HTML DependencyGraphProof where toHtml = toHtml . show . pPrint

instance DotRep DependencyGraphProof where
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
   coloredNodes = [ case nodeColorsA ! n of
                        Nothing -> (n,[label (int n)])
                        Just c  -> (n, [label (int n), LabelFontColor (head c), Color c])
                      | n <- G.vertices g]
   nodeColorsA  = A.listArray (A.bounds g) [ snd <$> find ((n `Set.member`) . Prelude.fst) (zip sccs colors)
                                             | n <- G.vertices g]
   coloredEdges = [ (a,b,att)
                       | (a,b) <- G.edges g
                       , let att = case (nodeColorsA ! a, nodeColorsA ! b) of
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
   coloredNodes = [ case True of
                      _ | n `Set.member` initial ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "red"), Color $ mkColor "red"])
                        | n `Set.member` reachable ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "green"), Color $ mkColor "green"])
                        | n `Set.member` inPath ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "rosybrown1"), Color $ mkColor "rosybrown1"])
                        | n `Set.member` outOfScope ->
                           (n,[label (int n), LabelFontColor (head $ mkColor "gray"), Color $ mkColor "gray"])
                        | otherwise -> (n,[label (int n)])
                      | n <- G.vertices gr]
   coloredEdges = [ (a,b, case True of
                            _ | a `Set.member` reachable && b `Set.member` reachable ->
                                 [Color $ mkColor "green"]
                              | a `Set.member` inPath && b `Set.member` inPath ->
                                 [Color $ mkColor "rosybrown1"]
                              | a `Set.member` outOfScope || b `Set.member` outOfScope ->
                                 [Color $ mkColor "gray"]
                              | otherwise -> [])
                    | (a,b) <- G.edges gr]

  dot NoCycles = Text (text "There are no cycles, so the system is terminating.") []


colors = cycle $ map mkColor ["darkorange", "hotpink", "hotpink4", "purple", "brown","red","green","yellow"]

-- ---------------
-- Implementation
-- ---------------
type GraphProcessor typ t mp =   (problem ~ Problem typ trs, Info info problem
                                 ,trs     ~ NarradarTRS t Var
                                 ,MkDPProblem typ (NarradarTRS t Var)
                                 ,Traversable (Problem typ)
                                 ,Pretty (Term t Var), Pretty typ
                                 ,Unify t, ICap t Var (typ, trs)
                                 ,Info info DependencyGraphProof
                                 ,Monad mp
                                 ) =>
                                    Problem typ (NarradarTRS t Var) -> Proof info mp problem

cycleProcessor, sccProcessor :: GraphProcessor typ t mp

sccProcessor problem@(getP -> dps@(DPTRS dd gr unif sig))
  | null cc   = success NoCycles problem
  | otherwise = andP (SCCs gr (map Set.fromList cc)) problem
                 [setP (restrictDPTRS (DPTRS dd gr unif sig) ciclo) problem | ciclo <- cc]
    where
      cc  = [vv | CyclicSCC vv <- GSCC.sccList gr]

cycleProcessor problem@(getP -> DPTRS dd gr unif sig)
  | null cc   = success NoCycles problem
  | otherwise = andP (Cycles gr) problem
                 [setP (restrictDPTRS (DPTRS dd gr unif sig) ciclo) problem | ciclo <- cc]
    where
      cc = cycles gr


