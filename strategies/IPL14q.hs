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
import Control.Parallel.Strategies (withStrategy)
import Data.List (nub)
import Data.Maybe
import Data.Traversable (Traversable)
import Data.Typeable
import qualified Data.Set as Set
import qualified Language.Prolog.Syntax as Prolog
import Narradar
import Narradar.Processor.RPO
import Narradar.Processor.RPO.SBV
import Narradar.Processor.WPO.SBV
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Framework.GraphViz
import Narradar.Processor.RelativeProblem
import MuTerm.Framework.Proof
import Narradar.Utils (pprTrace, Comparable(..))
import Common
import Text.Printf
import Prelude hiding (sum)

import Debug.Hoed.Observe

import Data.IORef
import System.IO.Unsafe

--main = runO $ gdmobservers "main" commonMain
main = commonMain nilObserver

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem IRewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance (-- Eq(EqModulo(NProblem (QRewritingN Id) Id))
         ) => Dispatch (NProblem (QRewritingN Id) Id) where
  dispatch = (withStrategy parallelize .)
               (ev >=> fix step >=> final)
    where
      step   = (fix dgI >=>
                     (inn `orElse1`
                      (ur >=> try qshrink) `orElse1`
                      (polo 1 1 >=> try qshrink) `orElse1`
                      redPair `orElse1`
                      graphT)
                  )
      inn    = apply ToInnermost
      innO p = gdmobservers "Innermost" applyO ToInnermost p
      graphT = gt1 -- rew .||. inst .||. narr
      redPair = sc `orElse1` msum -- .||. mpol Nothing Nothing
