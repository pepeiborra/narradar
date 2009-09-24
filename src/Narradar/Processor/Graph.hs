{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, ViewPatterns #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
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
import Data.Foldable (Foldable, foldMap)
import Data.List (find)
import Data.Traversable (Traversable)
import Data.Tree  as Tree
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
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
         , problem ~ DPProblem typ trs, ProblemInfo problem
         , MkDPProblem typ (NarradarTRS t Var), Traversable (DPProblem typ)
         , Unify t, ICap t Var (typ,trs)
         , Pretty (Term t Var), Pretty typ
         ) =>
    Processor DependencyGraphSCC (DPProblem typ (NarradarTRS t Var)) (DPProblem typ (NarradarTRS t Var)) where
  apply DependencyGraphSCC = sccProcessor


instance ( TermId t ~ Identifier id0, Ord id0
         , trs ~ NarradarTRS t Var
         , problem ~ DPProblem (InitialGoal t typ0) trs, ProblemInfo problem
         , MkDPProblem typ0 (NarradarTRS t Var), Traversable (DPProblem typ0)
         , HasId t, Unify t, Ord (Term t Var)
         , Pretty (Term t Var), Pretty typ0
         , ICap t Var (typ0,trs), ProblemColor problem, PprTPDBDot problem
         ) =>
    Processor DependencyGraphSCC
             (DPProblem (InitialGoal t typ0) (NarradarTRS t Var))
             (DPProblem (InitialGoal t typ0) (NarradarTRS t Var))
 where
  apply DependencyGraphSCC    = usableSCCsProcessor


instance ( trs ~ NarradarTRS t Var
         , problem ~ DPProblem typ trs, ProblemInfo problem
         , MkDPProblem typ (NarradarTRS t Var), Traversable (DPProblem typ)
         , HasId t, Unify t, Ord (Term t Var)
         , Pretty (Term t Var), Pretty typ
         , ICap t Var (typ,trs), ProblemColor problem, PprTPDBDot problem
         ) =>
    Processor DependencyGraphCycles (DPProblem typ (NarradarTRS t Var)) (DPProblem typ (NarradarTRS t Var)) where
  apply DependencyGraphCycles = cycleProcessor

-- --------------
-- Graph Proofs
-- --------------

data DependencyGraphProof = SCCs   Graph [Set Vertex]
                          | UsableSCCs Graph (Set Vertex)
                          | Cycles Graph
                          | NoCycles
                         deriving (Eq, Ord, Show)

instance Pretty DependencyGraphProof where
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

  dot NoCycles = Text (text "There are no cycles, so the system is terminating.") []

instance ProofInfo DependencyGraphProof

-- ---------------
-- Implementation
-- ---------------
type GraphProcessor typ t mp =   (problem ~ DPProblem typ trs, ProblemInfo problem
                                 ,trs     ~ NarradarTRS t Var
                                 ,MkDPProblem typ (NarradarTRS t Var)
                                 ,Traversable (DPProblem typ)
                                 ,Pretty (Term t Var), Pretty typ
                                 ,Unify t, ICap t Var (typ, trs)
                                 ,Monad mp
                                 ) =>
                                    DPProblem typ (NarradarTRS t Var) -> Proof mp problem

cycleProcessor, sccProcessor :: GraphProcessor typ t mp
usableSCCsProcessor :: (Identifier a ~ TermId t, Ord a) => GraphProcessor (InitialGoal t  typ0) t mp


sccProcessor problem@(getP -> dps@(DPTRS _ _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise = andP (SCCs gr (map Set.fromList cc)) problem
                 [mkDPProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where
      typ = getProblemType problem
      trs = getR problem
      dd  = rulesArray dps
      gr  = getEDG problem
      cc  = [vv | CyclicSCC vv <- GSCC.sccList gr]

cycleProcessor problem@(getP -> DPTRS dd _ unif sig)
  | null cc   = success NoCycles problem
  | otherwise = andP (Cycles gr) problem
                 [mkDPProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo) | ciclo <- cc]
    where
      cc = cycles gr
      gr = getEDG problem
      typ = getProblemType problem
      trs = getR problem

{-
usableSCCsProcessor :: (problem ~ DPProblem typ trs
                       ,trs     ~ NarradarTRS id v
                       ,t       ~ TermF id
                       ,v       ~ Var
                       ,typ     ~ InitialGoal id typ0
                       ,id      ~ Identifier id0
                       ,IsDPProblem typ, Traversable (DPProblem typ)
                       ,Ppr typ, HTML typ, HTMLClass typ
                       ,ICap t v problem
                       ,Ppr v, Ord v, Enum v, Ppr id, Ord id
                       ) =>
                            DPProblem typ trs -> Proof problem
-- TODO Think about the usableSCC processor.
-}

usableSCCsProcessor problem@(getP -> dps@(DPTRS dd _ unif sig))
  | null cc   = success NoCycles problem
  | otherwise =  andP (UsableSCCs gr reachable) problem
                 [mkDPProblem typ trs (restrictDPTRS (DPTRS dd gr unif sig) ciclo)
                      | ciclo <- cc, any (`Set.member` reachable) ciclo]
  where
   typ@InitialGoal{..} = getProblemType problem
   trs         = getR problem
   gr          = getEDG problem
   cc          = [vv | CyclicSCC vv <- GSCC.sccList gr]
   reachable   = Set.fromList (G.reachable gr =<< goal_pairs)
   goal_pairs  = [ i | (i,r) <- [0..] `zip` rules dps
                     , Just f <- [rootSymbol (lhs r)]
                     , unmarkDPSymbol f `Set.member` Set.fromList (goalId <$> goals_PType)]

usableSCCsProcessor p = sccProcessor p

