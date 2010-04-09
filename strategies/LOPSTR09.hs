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
  dispatch = rpoPlusTransforms >=> final

instance Dispatch (NProblem CNarrowing Id) where
  dispatch = rpoPlusTransformsPar >=> final

-- Narrowing Goal
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, HasTrie id) => Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, HasTrie id) => Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = rpoPlusTransforms >=> final

instance (Pretty (GenId id), Ord id, HasTrie id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) CNarrowingGen) (GId id)) where
  dispatch = rpoPlusTransformsPar >=> final

instance (Pretty (GenId id), Ord id, HasTrie id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) NarrowingGen) (GId id)) where
  dispatch = rpoPlusTransforms >=> final

-- Relative
instance (Dispatch (NProblem base id)
         ,Pretty id, Ord id, HasTrie id
         ,Pretty (TermN id)
         ,Pretty base, IsDPProblem base, MkProblem base (NTRS id), HasMinimality base
         ,PprTPDB (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch

dg = apply DependencyGraphSCC{useInverse=True}
sc = dg >=> try SubtermCriterion


rpoPlusTransforms
   = dg >=>
     repeatSolver 5 ((lpo .|. rpos .|. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTFFI)
    mpo  = apply (RPOProc MPOAF  Needed SMTFFI)
    lpos = apply (RPOProc LPOSAF Needed SMTFFI)
    rpo  = apply (RPOProc RPOAF  Needed SMTFFI)
    rpos = apply (RPOProc RPOSAF Needed SMTFFI)


rpoPlusTransformsPar = parallelize f where
 f = dg >=>
     repeatSolver 5 ( (lpo.||. rpos .||. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTSerial)
    rpos = apply (RPOProc RPOSAF Needed SMTSerial)


graphTransform = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
