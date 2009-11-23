#!/usr/bin/env runhaskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.Aprove
import Narradar.Processor.RPO
import Narradar.Processor.FLOPS08
import Narradar.Framework.GraphViz
import Lattice
--import Narradar.Utils

main = narradarMain listToMaybe


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getProblemType p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"

-- Rewriting
instance (Pretty (DPIdentifier a), Ord a) => Dispatch (NProblem Rewriting (DPIdentifier a)) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

instance (Pretty (DPIdentifier a), Ord a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

-- Narrowing Goal

instance (id  ~ DPIdentifier a, Ord a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (NarrowingGoal (DPIdentifier a)) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply (ComputeSafeAF bestHeu) >=> depGraph  >=>
                 apply (NarrowingGoalToRewriting bestHeu) >=>
                 dispatch)


sc = depGraph >=> try(apply SubtermCriterion)

rpoPlusTransforms rpo =  depGraph >=>
                         repeatSolver 5 (apply(RPOProc LPOAF (Yices 60)) .|. apply(RPOProc rpo (Yices 60)) .|. graphTransform >=>
                                         depGraph
                                         )


graphTransform = apply NarrowingP .|. apply FInstantiation .|. apply Instantiation
