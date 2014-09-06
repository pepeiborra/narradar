

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}

-- module LOPSTR09 where

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
import Narradar.Utils (pprTrace)
import Common

import Debug.Hoed.Observe

#ifndef WEB
import Narradar.Interface.Cli
--main = narradarMain id nilObserver
main = runO $ gdmobservers "main" (narradarMain id)
#else
import Narradar.Interface.Cgi
main = narradarCgi id
#endif



-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getFramework p))

--instance Dispatch thing where dispatch _ = error "missing dispatcher"

-- Prolog
--instance Dispatch PrologProblem where
--  dispatch = apply SKTransform >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = inn .|.
             (ev >=>
              lfpBounded 4 (dg >=>sc `orElse` lpo `orElse` rpos `orElse` gt2) >=>
              final)

instance (FrameworkId a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch =  ev >=>
              lfpBounded 4 (dg >=> sc `orElse` lpo `orElse` rpos `orElse` gt1) >=>
              final

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

instance (Pretty (DPIdentifier id), FrameworkId (GenId id), FrameworkId id) =>
     Dispatch (NProblem (InitialGoal (TermF (DPIdentifier id)) Narrowing) (DPIdentifier id)) where
   dispatch = (return .|. dgO) >=>
              apply NarrowingGoalToRelativeRewriting >=> dispatch

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch =  evO >=>
              lfpBounded 4 (dg >=> sc `orElse` lpo `orElse` rpos `orElse` gt1) >=>
              final

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = inn .|.
             (ev >=>
              lfpBounded 4 (dg >=>sc `orElse` lpo `orElse` rpos `orElse` gt2) >=>
              final)

instance (Pretty (GenId id), FrameworkId id) =>
 Dispatch (NProblem (InitialGoal (TermF (GId id)) INarrowingGen) (GId id)) where
  dispatch = dg >=> rpoPlus gt2 >=> final

instance (Pretty (GenId id), FrameworkId id
         ) => Dispatch (NProblem (InitialGoal (TermF (GId id)) NarrowingGen) (GId id)) where
   dispatch = -- inn .|.
              (dg  >=> final)
     where
    lpo  = apply (RPOProc LPOAF  Needed SMTFFI True)
    mpo  = apply (RPOProc MPOAF  Needed SMTFFI True)
    lpos = apply (RPOProc LPOSAF Needed SMTFFI True)
    rpo  = apply (RPOProc RPOAF  Needed SMTFFI True)
    rpos = apply (RPOProc RPOSAF Needed SMTFFI True)

-- Relative
instance (Dispatch (NProblem base id)
         ,FrameworkProblemN base id
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegular >=> dispatch
