{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Narradar.Framework.GraphViz (
     module Narradar.Framework.GraphViz,
     module MuTerm.Framework.GraphViz,
     module MuTerm.Framework.DotRep,
 ) where

import Control.Applicative
import Control.Monad
import Data.Graph
import Data.Foldable (toList, Foldable)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List hiding (unlines)
import Data.Maybe
import Data.Traversable (Traversable)
import Data.GraphViz.Attributes

import Prelude hiding (unlines)
#ifdef DEBUG
import System.Process
import Text.Printf
#endif

import qualified Data.Term.Var as Term
import qualified Language.Prolog.Syntax as Prolog

import MuTerm.Framework.DotRep
import MuTerm.Framework.GraphViz
import MuTerm.Framework.Proof
import MuTerm.Framework.Problem

import Narradar.Types.ArgumentFiltering (fromAF)
import Narradar.Types.Problem
import Narradar.Types.Problem.Infinitary
import Narradar.Types
import Narradar.Utils



-- instance Ppr a => DotRep a where dotSimple x = Text (showPpr x)[]
{-
    proofnode done (SomeInfo (DependencyGraph gr)) par | done || showFailedPaths = do
      (cl, nn) <- cluster (attribute ("shape", "ellipse") >> pprGraph gr [])
      case nn of
        []   -> return par
        me:_ -> do case par of
                     N n             -> edge n me ([("lhead", show cl)] ++ doneEdge done)
                     Cluster (cl',n) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)]
                   return (Cluster (cl, N me))

    proofnode done (SomeInfo (SCCGraph gr sccs)) par = do
      (cl, nn) <- cluster (
                    attribute ("shape", "ellipse") >>
                    pprGraph gr (zip sccs (cycle ["yellow","darkorange"
                                                 , "hotpink", "hotpink4", "purple", "brown","red","green"])))
      case (nn,par) of
        ([]  , _  )             -> return par
        (me:_, N n)             -> edge n me ([("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
        (me:_, Cluster (cl',n)) -> edge (getParentNode n) me [("ltail", show cl'), ("lhead", show cl)] >> return (Cluster (cl, N me))


    proofnode done (SomeInfo (UsableGraph gr reachable)) par = do
      (cl, nn) <- cluster (attribute ("shape", "ellipse") >> (pprGraph gr [(reachable,"blue")]))
      case (nn,par) of
        ([]  , _  )             -> return par
        (me:_, N n)             -> edge n me ([("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
        (me:_, Cluster (cl',n)) -> edge (getParentNode n) me ([("ltail", show cl'), ("lhead", show cl)] ++ doneEdge done) >> return (Cluster (cl, N me))
-}

instance (PprTPDBDot (NarradarProblem typ id), ProblemColor (NarradarProblem typ id)) =>
    DotRep (NarradarProblem typ id) where
    dot p = Text (pprTPDBdot p) [ Color [problemColor p]
                                , Shape BoxShape
                                , Style (Stl Bold Nothing)
                                , FontName "monospace"
                                , FontSize 10
                                , Margin (PVal (PointD 0.2 0.2))]

class PprTPDBDot p where pprTPDBdot :: p -> Doc
instance (Pretty id, Pretty (Prolog.Term' id Term.Var)) => PprTPDBDot (PrologProblem id) where
  pprTPDBdot PrologProblem{..} =
    vcat (map pPrint program) $$
    vcat [text "%Query: " <+> (pPrint g) | g <- goals]

instance (IsDPProblem typ, HasRules t v trs, GetVars v trs, Pretty v, Pretty (Term t v)
         ,HasId t, Pretty (TermId t), Foldable t, Traversable (DPProblem typ)
         ) => PprTPDBDot (DPProblem typ trs) where
  pprTPDBdot p = vcat
     [parens( text "VAR" <+> (hsep $ map pPrint $ toList $ getVars p))
     ,parens( text "PAIRS" $$
              nest 1 (vcat $ map pprRule $ rules $ getP p))
     ,parens( text "RULES" $$
              nest 1 (vcat $ map pprRule $ rules $ getR p))
     ]
   where
        pprRule (a:->b) = pprTerm a <+> text "->" <+> pprTerm b
        pprTerm = foldTerm pPrint f
        f t@(getId -> Just id)
            | null tt = pPrint id
            | otherwise = pPrint id <> parens (hcat$ punctuate comma tt)
         where tt = toList t
{-
instance (Pretty id, PprTPDBDot (DPProblem typ trs)) =>
    PprTPDBDot (DPProblem (InitialGoal id typ) trs) where
    pprTPDBdot (InitialGoalProblem goal p) = pprTPDBdot p ++ "\\l" ++
                                              "(AF\\l" ++ pprAF pi ++ ")" ++
                                               "\\l"
-}

instance (Pretty trs, PprTPDBDot (DPProblem Rewriting trs)) => PprTPDBDot (DPProblem Narrowing trs) where
  pprTPDBdot p = pprTPDBdot (mkDPProblem Rewriting (getR p) (getP p)) $$
                 text "(STRATEGY Narrowing)"

instance (Pretty trs, PprTPDBDot (DPProblem typ trs)) =>
  PprTPDBDot (DPProblem (Infinitary trs typ) trs) where
   pprTPDBdot (InfinitaryProblem pi p) = pprTPDBdot p $$
                                         parens(text "AF" <+> pprAF pi)


pprAF af = vcat [ hsep (punctuate comma [ pPrint f <> colon <+> either (pPrint.id) (pPrint.toList) aa | (f, aa) <- xx])
                      | xx <- chunks 4 $ Map.toList $ fromAF af]


class ProblemColor p where problemColor :: p -> Color
instance ProblemColor typ where problemColor _ = ColorName "black"
instance (IsDPProblem typ, ProblemColor typ) =>
    ProblemColor (DPProblem typ trs) where problemColor = problemColor . getProblemType
instance ProblemColor (PrologProblem id) where problemColor _ = ColorName "#F6D106"
instance ProblemColor Rewriting where problemColor _ = ColorName "#EAAAFF"
instance ProblemColor Narrowing where problemColor _ = ColorName "#4488C9"
instance ProblemColor CNarrowing where problemColor _ = ColorName "#FD6802"


#ifdef DEBUG
--debugDot x = let t = "temp" in writeFile (t ++ ".dot") (pprDot' (PprDot True) x) >> system (printf "dot %s.dot -O -Tpdf && open %s.dot.pdf" t t)
#endif
