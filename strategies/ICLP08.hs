#!/usr/bin/env runhaskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.DeepSeq
import Control.Monad
import Control.Monad.Stream
import Control.Parallel.Strategies
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.LOPSTR09
import Narradar.Framework.GraphViz
import Lattice
import Narradar.Utils (pprTrace)

instance IsMZero Stream where
  isMZero = null . runStream

--import Narradar.Utils

main = narradarMain (listToMaybe)


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getProblemType p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"


-- Prolog
instance Dispatch PrologProblem where
  dispatch = apply SKTransform >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = sc >=> rpoPlusTransforms >=> final

instance (id ~ DPIdentifier a, Pretty id, HasTrie a, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = sc >=> rpoPlusTransformsPar >=> final

-- Narrowing
instance Dispatch (NProblem Narrowing Id) where
  dispatch = dg >=> apply (NarrowingToRewritingICLP08 (simpleHeu innermost)) >=> dispatch

-- Narrowing Goal
instance Dispatch (NProblem (NarrowingGoal Id) Id) where
  dispatch = dispatch . mkDerivedDPProblem narrowing


dg = apply DependencyGraphSCC{useInverse=False}
sc = dg >=> try SubtermCriterion

rpoPlusTransforms
   = repeatSolver 5 ((lpo .|. rpos .|. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  None SMTFFI)
    mpo  = apply (RPOProc MPOAF  None SMTFFI)
    lpos = apply (RPOProc LPOSAF None SMTFFI)
    rpo  = apply (RPOProc RPOAF  None SMTFFI)
    rpos = apply (RPOProc RPOSAF None SMTFFI)


rpoPlusTransformsPar = parallelize f where
 f = dg >=>
     repeatSolver 5 ( (lpo.||. rpos .||. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  None SMTSerial)
    rpos = apply (RPOProc RPOSAF None SMTSerial)


graphTransform = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
