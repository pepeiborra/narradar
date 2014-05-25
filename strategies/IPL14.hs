{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}

-- module IPL14 where

import Control.Monad
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.LOPSTR09
import Narradar.Framework.GraphViz
import Lattice ()
import Narradar.Utils (pprTrace)

#ifndef WEB
import Narradar.Interface.Cli
main = narradarMain listToMaybe
#else
import Narradar.Interface.Cgi
main = narradarCgi listToMaybe
#endif


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("This version of Narradar does not handle problems of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "This version of Narradar does not support the input problem."

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = ev >=> (inn .|. (rpoPlus gt2 >=> final))

instance (Pretty (DPIdentifier a), Hashable a, Ord a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = ev >=> rpoPlus gt1 >=> final

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch = ev >=> rpoPlus gt1 >=> final

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = ev >=> ( inn .|.
                      (rpoPlus gt2 >=> final))
-- Relative
instance Dispatch (NProblem (Relative (NTRS Id) (InitialGoal (TermF Id) Rewriting)) Id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

instance (Dispatch (NProblem base id)
         ,Pretty id, Ord id, Hashable id
         ,Pretty (TermN id)
         ,Pretty base, IsDPProblem base, MkProblem base (NTRS id), HasMinimality base
         ,PprTPDB (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

-- Solvers
dg_ = DependencyGraphSCC{useInverse=True}
dg = apply dg_
sc = try(apply SubtermCriterion)
dgsc = lfp(dg >=> sc)
ev = apply ExtraVarsP
inn = apply ToInnermost >=> dispatch

rpoPlus transform
   = repeatSolver 2 (dgsc >=> (lpo .|. rpos .|. transform))
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTFFI True)
    mpo  = apply (RPOProc MPOAF  Needed SMTFFI True)
    lpos = apply (RPOProc LPOSAF Needed SMTFFI True)
    rpo  = apply (RPOProc RPOAF  Needed SMTFFI True)
    rpos = apply (RPOProc RPOSAF Needed SMTFFI True)

gt1 = apply RewritingP .||. apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
gt2 = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
