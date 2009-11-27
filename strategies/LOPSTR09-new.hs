#!/usr/bin/env runhaskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad
import Control.Monad.Stream
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.LOPSTR09
import Narradar.Framework.GraphViz
import Lattice

instance IsMZero Stream where
  isMZero = null . runStream

--import Narradar.Utils

main = narradarMain (listToMaybe.runStream)


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getProblemType p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"


-- Prolog
instance Dispatch PrologProblem where
  dispatch = apply SKTransform >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

instance (id ~ DPIdentifier a, Pretty id, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

-- Narrowing Goal
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id) => Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id) => Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

instance (Pretty (GenId id), Ord id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) CNarrowingGen) (GId id)) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

instance (Pretty (GenId id), Ord id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) NarrowingGen) (GId id)) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

-- Relative
instance (Dispatch (NProblem base id)
         ,Pretty id, Ord id, Pretty base, Pretty (TermN id)
         ,IsDPProblem base, MkProblem base (NTRS id), HasMinimality base
         ,PprTPDB (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch

sc = apply DependencyGraphSCC >=> apply SubtermCriterion

rpoPlusTransforms rpo =  depGraph >=>
                         try (apply (RPOProc LPOAF (Yices 60)) >=> depGraph) >=>
                         try (repeatSolver 5 (graphTransform .|. apply (RPOProc rpo (Yices 60)) >=> depGraph)) >=>
                         apply (RPOProc RPOAF (Yices 60))


graphTransform = apply NarrowingP .|. apply FInstantiation .|. apply Instantiation
