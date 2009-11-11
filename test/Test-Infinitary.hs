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
import Narradar.Framework.GraphViz
import Lattice
--import Narradar.Utils

main = narradarMain listToMaybe


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getProblemType p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"


-- Prolog
instance Dispatch PrologProblem where
--    dispatch = apply SKTransformInfinitary >=> dispatch
    dispatch = apply SKTransformNarrowing >=> dispatch

-- Rewriting
instance (Pretty (DPIdentifier a), Ord a) => Dispatch (NProblem Rewriting (DPIdentifier a)) where
  dispatch = mkDispatcher $ fixSolver (apply DependencyGraphSCC >=> apply (RPOProc LPO Yices))

instance (Pretty (DPIdentifier a), Ord a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = mkDispatcher (rpoPlusTransforms RPOSAF)

-- Narrowing
instance (Pretty id, Pretty (DPIdentifier id), Ord id, Lattice (AF_ (DPIdentifier id))) =>
    Dispatch (NProblem Narrowing (DPIdentifier id)) where
  dispatch = mkDispatcher (rpoPlusTransforms LPOSAF)

-- Narrowing Goal
instance (Pretty (DPIdentifier id), Ord id, Lattice (AF_ (DPIdentifier id))) => Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply (NarrowingGoalToInfinitary bestHeu) >=> dispatch
instance (Pretty (DPIdentifier id), Ord id, Lattice (AF_ (DPIdentifier id))) => Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply (NarrowingGoalToInfinitary bestHeu) >=> dispatch

-- Infinitary
instance (id  ~ DPIdentifier a, Ord a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) Rewriting) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply DependencyGraphSCC >=>
                 apply (InfinitaryToRewriting bestHeu) >=>
                 dispatch)

instance (id  ~ DPIdentifier a, Ord a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) IRewriting) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply DependencyGraphSCC >=>
                 apply (InfinitaryToRewriting bestHeu) >=>
                 dispatch)

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
         ,IsDPProblem base, MkProblem base (NTRS id)
         ,PprTPDBDot (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch

proofByAprove = aprove

rpoPlusTransforms rpo =  apply DependencyGraphSCC >=>
                         fixSolver (apply (RPOProc rpo Yices) .|. graphTransform >=>
                                    apply DependencyGraphSCC
                                   )


graphTransform = apply NarrowingP .|. apply FInstantiation .|. apply Instantiation

{-
instance (Pretty id, Pretty (DPIdentifier id), Ord id, Lattice (AF_ (Identifier id))) =>
    Dispatch (DPProblem  Narrowing (NarradarTRS (TermF (DPIdentifier id)) Var)) where
  dispatch = mkDispatcher(
                         apply DependencyGraphCycles
                     >=> apply (NarrowingToRewritingICLP08 bestHeu)
                     >=> apply (AproveServer 10 Default)
                         )
-}