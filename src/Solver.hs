module Solver where

import Problem
import NarrowingProblem
import Aprove
import DPairs
import Types
import Operad

import Text.XHtml

solveNarrowing, solveNarrowingWeb, solveNarrowingLocal :: (AnnotateWithPos f f, Types.Ppr f) => TRS Identifier f -> IO (ProblemProgress Html f)
solveNarrowing = solveNarrowingLocal


solveNarrowingWeb   trs@TRS{}      = fmap runPP . solveProblemM aproveWebProc . solveProblem afProcessor . inE . cycleProcessor . mkNDPProblem $ trs

solveNarrowingLocal' path trs@TRS{}= fmap runPP . solveProblemM (aproveProc path) . solveProblem afProcessor . inE . cycleProcessor . mkNDPProblem $ trs

solveNarrowingLocal trs@TRS{} = solveNarrowingLocal' "/usr/local/lib/aprove/runme" trs

solveNarrowingSrv trs@TRS{}= fmap runPP . solveProblemM aproveSrvProc . solveProblem afProcessor . inE . cycleProcessor . mkNDPProblem $ trs
