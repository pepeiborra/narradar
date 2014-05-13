

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE CPP #-}


module LOPSTR09 where

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
import Lattice
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
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"

-- Prolog
instance Dispatch PrologProblem where
  dispatch = apply SKTransform >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = ev >=> (inn .|. (dg >=> rpoPlus gt2 >=> final))

instance (Pretty (DPIdentifier a), Hashable a, Ord a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch = ev >=> sc >=> dg >=> rpoPlus gt1 >=> final

-- Narrowing
instance Dispatch (NProblem Narrowing Id) where
  dispatch = ev >=> dg >=> rpoPlus gt2 >=> final

instance Dispatch (NProblem CNarrowing Id) where
  dispatch = ev >=> dg >=> rpoPlus gt2 >=> final

{--- Narrowing Goal
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, Hashable id) => Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, Hashable id) => Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply NarrowingGoalToRelativeRewriting >=> dispatch
-}

-- Initial Goal
type GId id = DPIdentifier (GenId id)

-- instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, Hashable id) =>
--     Dispatch (NProblem (InitialGoal (TermF (DPIdentifier id)) Narrowing) (DPIdentifier id)) where
--   dispatch = (return .|. dg) >=>
--              apply NarrowingGoalToRelativeRewriting >=> dispatch

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch = ev >=> dg >=> rpoPlus gt1 >=> final

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = ev >=> ( -- (inn >=> dispatch) .|.
                      (dg >=> rpoPlus gt2 >=> final)
                    )

--instance (Pretty (GenId id), Ord id, Hashable id) =>
-- Dispatch (NProblem (InitialGoal (TermF (GId id)) INarrowingGen) (GId id)) where
--  dispatch = dg >=> rpoPlus gt2 >=> final

-- instance (Pretty (GenId id), Ord id, Hashable id) => Dispatch (NProblem (InitialGoal (TermF (GId id)) NarrowingGen) (GId id)) where
--   dispatch = (inn >=> dispatch) .|.
--              (dg  >=> rpoPlus gt2 >=> final)

-- Relative
instance (Dispatch (NProblem base id)
         ,Pretty id, Ord id, Hashable id
         ,Pretty (TermN id)
         ,Pretty base, IsDPProblem base, MkProblem base (NTRS id), HasMinimality base
         ,PprTPDB (NProblem base id), ProblemColor (NProblem base id)
         ,Pretty (NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch

dg = apply DependencyGraphSCC{useInverse=True}
sc = dg >=> try SubtermCriterion
ev = apply ExtraVarsP
inn = apply ToInnermost >=> dispatch

rpoPlus transform
   = repeatSolver 10 ((lpo .|. rpos .|. transform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTFFI True)
    mpo  = apply (RPOProc MPOAF  Needed SMTFFI True)
    lpos = apply (RPOProc LPOSAF Needed SMTFFI True)
    rpo  = apply (RPOProc RPOAF  Needed SMTFFI True)
    rpos = apply (RPOProc RPOSAF Needed SMTFFI True)

rpoPlusPar transform = parallelize f where
 f = repeatSolver 5 ( (lpo.||. rpos .||. transform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTSerial True)
    rpos = apply (RPOProc RPOSAF Needed SMTSerial True)


gt1 = apply RewritingP .||. apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
gt2 = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
