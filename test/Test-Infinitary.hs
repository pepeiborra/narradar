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
    dispatch = apply SKTransformInfinitary >=> dispatch

-- Rewriting
instance (Pretty (DPIdentifier a), Ord a) => Dispatch (NProblem Rewriting (DPIdentifier a)) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

instance (Pretty (DPIdentifier a), Ord a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = mkDispatcher (sc >=> rpoPlusTransforms LPOSAF)

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

sc = apply DependencyGraphSCC >=> apply SubtermCriterion

rpoPlusTransforms rpo =  apply DependencyGraphSCC >=>
                         repeatSolver 5 (apply (RPOProc rpo Yices) .|. graphTransform >=>
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