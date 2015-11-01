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

main = runO $ gdmobservers "main" commonMain

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance () => Dispatch (NProblem IRewriting Id) where
  dispatch = qr >=> dispatch

-- Rewriting
instance (-- Eq(EqModulo(NProblem (QRewritingN Id) Id))
         ) => Dispatch (NProblem (QRewritingN Id) Id) where
  dispatch = -- (withStrategy parallelize .)
               (dg >=> instO >=> dg >=> final)
    where
      step   = (fix dgI >=>
                     (inn `orElse1`
                      redPair `orElse1`
                      graphT)
                  )
      inn    = apply ToInnermost
      graphT = gt1
      redPair = sc
