{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
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
import Data.Typeable
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import MuTerm.Framework.Strategy
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Framework.GraphViz
import Narradar.Utils (pprTrace)
import Common

import Debug.Hoed.Observe

#ifndef WEB
import Narradar.Interface.Cli
main = narradarMain (id :: [a] -> [a]) nilObserver
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
  dispatch = inn .|.
             (ev >=>
              lfpBounded 4 (dg >=>sc `orElse` lpo `orElse` rpos `orElse` gt2) >=>
              final)

instance (FrameworkId a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch =  ev >=>
              lfpBounded 4 (dg >=> sc `orElse` lpo `orElse` rpos `orElse` gt1) >=>
              final

-- Initial Goal
type GId id = DPIdentifier (GenId id)

instance Dispatch (NProblem (InitialGoal (TermF Id) IRewriting) Id) where
  dispatch = apply LocalToGlobalP >=> dispatch

instance Dispatch (NProblem (InitialGoal (TermF Id) Rewriting) Id) where
  dispatch = apply LocalToGlobalP >=> dispatch

-- Relative
instance Dispatch (NProblem (Relative (NTRS Id) (InitialGoal (TermF Id) Rewriting)) Id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

instance (Dispatch (NProblem base id)
         ,FrameworkProblemN base id
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch
