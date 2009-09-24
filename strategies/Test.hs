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
import Narradar.Processor.Aprove
import Narradar.Processor.RPO
import Lattice
--import Narradar.Utils

try = apply -- proc p = if  apply proc p
tryS = applySearch

main = narradarMain listToMaybe


instance Dispatch thing where dispatch _ = error "missing dispatcher"

instance Dispatch (PrologProblem String) where
    dispatch = prologP_sk >=> dispatch

instance (IsDPProblem typ, Pretty typ) => Dispatch (DPProblem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getProblemType p))


instance () => Dispatch (DPProblem Rewriting (NTRS (Identifier String) Var)) where
  dispatch = mkDispatcher $ fixSolver (try DependencyGraphSCC >=> try (RPOProc LPO Yices))

instance (id ~ Identifier a, Pretty id, Ord a) => Dispatch (DPProblem IRewriting (NTRS id Var)) where
  dispatch = mkDispatcher rpoPlusTransforms


instance (Pretty id, Pretty (Identifier id), Ord id, Lattice (AF_ (Identifier id))) =>
    Dispatch (DPProblem  Narrowing (NTRS (Identifier id) Var)) where
  dispatch = mkDispatcher rpoPlusTransforms

instance (Pretty id, Ord id, Lattice (AF_ id), Dispatch (DPProblem  Rewriting (NTRS id Var))) =>
    Dispatch (DPProblem  (InitialGoal (TermF id) Narrowing) (NTRS id Var)) where
  dispatch = mkDispatcher goalNarrowingByInfinitary

instance (Pretty id, Ord id, Lattice (AF_ id),
                 Dispatch (DPProblem IRewriting (NTRS id Var))) =>
    Dispatch (DPProblem  (InitialGoal (TermF id) CNarrowing) (NTRS id Var)) where
  dispatch = mkDispatcher goalNarrowingByInfinitary

goalNarrowingByInfinitary =
                 apply InitialGoalNarrowingToInfinitaryRewriting >=>
                 try DependencyGraphSCC >=>
                 try (InfinitaryToRewriting bestHeu) >=>
                 proofByAprove

proofByAprove = aprove

rpoPlusTransforms =  apply DependencyGraphSCC >=>
--                     apply ExtraVarsP >=>
                     rpo .|. return >=>
                     fixSolver (apply DependencyGraphSCC >=>
                                graphTransform >=>
                                apply DependencyGraphSCC >=>
                                rpo .|. return)


graphTransform = try NarrowingP .|. try FInstantiation .|. try Instantiation

{-
instance (Pretty id, Pretty (Identifier id), Ord id, Lattice (AF_ (Identifier id))) =>
    Dispatch (DPProblem  Narrowing (NarradarTRS (TermF (Identifier id)) Var)) where
  dispatch = mkDispatcher(
                         try DependencyGraphCycles
                     >=> try (NarrowingToRewritingICLP08 bestHeu)
                     >=> try (AproveServer 10 Default)
                         )
-}