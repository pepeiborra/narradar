{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}

-- module IPL14 where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Free
import Data.List (nub)
import Data.Maybe
import Data.Foldable as F
import Data.Traversable (Traversable)
import Data.Typeable
import qualified Data.Set as Set
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Framework.GraphViz
import Narradar.Utils (pprTrace, Comparable(..))
import Common
import Text.Printf

import Debug.Hoed.Observe

import Data.IORef
import System.IO.Unsafe

#ifndef WEB
import Narradar.Interface.Cli
main = do
  runO$ narradarMain (id :: [a] -> [a]) nilObserver
  lpos <- readIORef lpoCounter
  let lpoUnique = length (nub lpos)
  printf "Counted %d calls to lpo, %d unique" (length lpos) lpoUnique
#else
import Narradar.Interface.Cgi
main = narradarCgi (id :: [a] -> [a])
#endif


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("This version of Narradar does not handle problems of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "This version of Narradar does not support the input problem."

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem IRewriting Id) where
  dispatch = qr >=> dispatch

qrO p = gdmobservers "QRewriting" applyO RewritingToQRewriting p
qr p = apply RewritingToQRewriting p

-- Rewriting
instance (-- Eq(EqModulo(NProblem (QRewritingN Id) Id))
         ) => Dispatch (NProblem (QRewritingN Id) Id) where
  dispatch = ev
             >=> lfpBounded 5 ( lfp dgInnU >=> (sc `orElse` lpo `orElse` rpos `orElse` (narr .|. inst .|. finst )))
--             >=> dg >=> try (inn `orElse` ur) >=> lpo >=> dg
             >=> final
    where
      dgInnU = dgI `ifSuccessOrElse` inn `orElse` ur
      inn    = apply ToInnermost
      innO p = gdmobservers "Innermost" applyO ToInnermost p

ifSuccessOrElse strat otherwise prob =
  case strat prob of
    proof@(Impure Success{}) -> proof
    proof -> (otherwise `orElse` (\_ -> proof)) prob

-- Initial Goal
type GId id = DPIdentifier (GenId id)

-- Relative
instance Dispatch (NProblem (Relative (NTRS Id) (InitialGoal (TermF Id) Rewriting)) Id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

instance (Dispatch (NProblem base id)
         ,FrameworkProblemN base id
         ,PprTPDB (NProblem base id)
         ,Ord(NProblem base id)
         ) => Dispatch (NProblem (Relative (NTRS id) base) id) where
  dispatch = apply RelativeToRegularIPL14 >=> dispatch

lpoCounter :: IORef [Comparable]
lpoCounter = unsafePerformIO $ do
  c <- newIORef []
  return c
