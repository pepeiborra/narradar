module Solver where

import Problem
import NarrowingProblem
import Aprove
import DPairs
import Types
import Operad

import Text.XHtml

solveNarrowing :: (AnnotateWithPos f f, Types.Ppr f) => TRS Identifier f -> IO (ProblemProgress Html f)
solveNarrowing trs@TRS{}= solveProblemM aproveWebProc . solveProblem afProcessor . cycleProcessor . mkNDPProblem $ trs