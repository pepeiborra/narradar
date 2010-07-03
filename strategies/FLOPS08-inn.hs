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
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.RPO
import Narradar.Processor.FLOPS08
import Narradar.Processor.LOPSTR09
import Lattice

import Narradar.Interface.Cli
main = narradarMain listToMaybe


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"

-- Prolog
instance Dispatch PrologProblem where
  dispatch = apply SKTransform >=> dispatch

-- Rewriting
instance (Pretty (DPIdentifier a), Ord a, HasTrie a) => Dispatch (NProblem Rewriting (DPIdentifier a)) where
  dispatch = ev >=> (inn .|. (dg >=> rpoPlusTransforms >=> final))

instance (Pretty (DPIdentifier a), Ord a, HasTrie a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = sc >=> rpoPlusTransforms >=> final

-- Narrowing Goal

instance (id  ~ DPIdentifier a, Ord a, Lattice (AF_ id), Pretty id, HasTrie a) =>
           Dispatch (NProblem (InitialGoal (TermF (DPIdentifier a)) Narrowing) (DPIdentifier a)) where
  dispatch = apply (ComputeSafeAF (simpleHeu innermost)) >=>
             dg  >=>
             apply (NarrowingGoalToRewriting bestHeu) >=>
             dispatch

dg  = apply DependencyGraphSCC{useInverse=True}
sc  = apply SubtermCriterion
ev  = apply ExtraVarsP
inn = apply ToInnermost >=> dispatch

rpoPlusTransforms
   = repeatSolver 5 ( (sc .|. lpo .|. rpos .|. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTFFI)
    lpos = apply (RPOProc LPOSAF Needed SMTFFI)
    rpos = apply (RPOProc RPOSAF Needed SMTFFI)

graphTransform = apply NarrowingP .|. apply FInstantiation .|. apply Instantiation
