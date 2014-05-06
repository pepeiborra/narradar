
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module ICLP08 where

import Control.Monad
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.LOPSTR09
import Narradar.Processor.NarrowingProblem
import Narradar.Framework.GraphViz
import Lattice

#ifndef WEB
import Narradar.Interface.Cli
main = narradarMain listToMaybe
#else
import Narradar.Interface.Cgi
main = narradarCgi listToMaybe
#endif



-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"


-- Prolog
instance Dispatch PrologProblem where
  dispatch = apply SKTransform >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = sc >=> rpoPlusTransforms >=> final

instance (id ~ DPIdentifier a, Pretty id, Hashable a, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = sc >=> rpoPlusTransformsPar >=> final

-- Narrowing
instance Dispatch (NProblem Narrowing Id) where
--  dispatch = dg >=> apply NarrowingToRewritingICLP08_SCC{heuristic=simpleHeu innermost,usableRules=True} >=> dispatch
  dispatch = dg >=> rpoPlusTransforms >=> final

-- Narrowing Goal
instance Dispatch (NProblem (InitialGoal (TermF Id) Narrowing) Id) where
  dispatch = dispatch . mkDerivedDPProblem narrowing
instance Dispatch (NProblem (NarrowingGoal Id) Id) where
  dispatch = dispatch . mkDerivedDPProblem narrowing


dg = apply DependencyGraphSCC{useInverse=True}
sc = dg >=> try SubtermCriterion

rpoPlusTransforms
   = repeatSolver 5 ((lpo .|. rpos .|. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  None SMTSerial)
    mpo  = apply (RPOProc MPOAF  None SMTSerial)
    lpos = apply (RPOProc LPOSAF None SMTSerial)
    rpo  = apply (RPOProc RPOAF  None SMTSerial)
    rpos = apply (RPOProc RPOSAF None SMTSerial)


rpoPlusTransformsPar = parallelize f where
 f = dg >=>
     repeatSolver 5 ( (lpo.||. rpos .||. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  None SMTSerial)
    rpos = apply (RPOProc RPOSAF None SMTSerial)


graphTransform = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
