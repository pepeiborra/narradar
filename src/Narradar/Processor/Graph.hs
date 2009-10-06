{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, ViewPatterns #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

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


instance ( TermId t ~ Identifier id0, Ord id0
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
  apply DependencyGraphSCC p@InitialGoalProblem{dgraph=dg@DGraph{..}, baseProblem = (getP -> dps@(DPTRS dd gr unif sig))}
   = do
    let nodes = Set.fromList $ catMaybes (map (`lookupNode` dg) (toList dd))

        gr'   = buildG (bounds gr)
                       [ (i,o) | (i,o) <- edges gr
                               , i `Set.member` nodes
                               , o `Set.member` nodes]

        cc   = [vv | CyclicSCC vv <- GSCC.sccList gr']

    if null cc
     then success NoCycles p
     else andP (UsableSCCs gr nodes) p
               [setP (restrictDPTRS (DPTRS dd gr unif sig) ciclo) p | ciclo <- cc]
    where

-- --------------
-- Graph Proofs
-- --------------

data DependencyGraphProof = SCCs   Graph [Set Vertex]
                          | UsableSCCs Graph (Set Vertex)
                          | Cycles Graph
                          | NoCycles
                         deriving (Eq, Ord, Show)

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
                   in  Nodes graph [] n n

  dot (SCCs g sccs) = Nodes coloredGraph [] (fst $ head coloredNodes) (fst $ head coloredNodes) where
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
   colors = cycle $ map mkColor ["yellow","darkorange", "hotpink", "hotpink4", "purple", "brown","red","green"]

-- TODO Improve the usable SCCs graphviz output
  dot (UsableSCCs g sccs) = Nodes coloredGraph [] (fst $ head coloredNodes) (fst $ head coloredNodes) where
   coloredGraph = FGL.mkGraph coloredNodes coloredEdges
   coloredNodes = [ if n `Set.member` sccs
                        then (n,[label (int n), LabelFontColor (head $ mkColor "yellow"), Color $ mkColor "yellow"])
                        else (n,[label (int n)])
                      | n <- G.vertices g]
   coloredEdges = [ (a,b, if a `Set.member` sccs && b `Set.member` sccs
                            then [Color $ mkColor "yellow"]
                            else [])
                    | (a,b) <- G.edges g]

  dot NoCycles = Text (text "There are no cycles, so the system is terminating.") []

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


