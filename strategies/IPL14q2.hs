{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
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
import Control.Monad hiding (msum)

import Data.List (nub)
import Data.Maybe
import Data.Traversable (Traversable)
import Data.Typeable
import qualified Data.Set as Set
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Processor.RPO
import Narradar.Processor.RPO.Z3
import Narradar.Processor.WPO.Z3
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Framework.GraphViz
import Narradar.Processor.RelativeProblem
import Narradar.Utils (pprTrace, Comparable(..))
import Common
import Text.Printf
import Prelude hiding (sum)

import Debug.Hoed.Observe

import Data.IORef
import System.IO.Unsafe

main = commonMain

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem IRewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance (-- Eq(EqModulo(NProblem (QRewritingN Id) Id))
         ) => Dispatch (NProblem (QRewritingN Id) Id) where
  dispatch = ev
             >=> dgI >=> ur
             >=> ((try inst >=> try(polo 0 2) >=> msum >=> dgI)
                 .|.
                  lfpBounded 20 (step (const mzero) (const mzero) gt1))
             >=> final
    where
      step rr rp tf = (dg >=>
                        (inn `orElse`
                        ((ur`orElse`rr) >=> try qshrink) `orElse`
                        rp `orElse`
                        tf)
                  )
      inn    = apply ToInnermost
      innO p = gdmobservers "Innermost" applyO ToInnermost p
