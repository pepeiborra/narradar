{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}

-- module IPL14 where
import Control.DeepSeq
import Control.Monad ( (>=>), (>>), forM_ )
import Data.Maybe
import Data.Typeable
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import MuTerm.Framework.Strategy
import Narradar
import Narradar.Processor.RPO.SBV
import Narradar.Processor.WPO.SBV
--import Narradar.Processor.RPO.YicesPipe
--import Narradar.Processor.WPO.YicesPipe
import Narradar.Processor.NonDP
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Framework.GraphViz
import Narradar.Utils (pprTrace)
import Common
import Prelude hiding (max, sum)

import Debug.Hoed.Observe

main = commonMain

-- Rewriting
-- todo: conversion to innermost
instance () => Dispatch (NProblem (NonDP Rewriting) Id) where
  dispatch = lfpBounded 2 (noRules `orElse` poloU) >=> final

instance (FrameworkId a, HasArity a) => Dispatch (NProblem IRewriting (DPIdentifier a)) where
  dispatch =  ev >=>
              lfpBounded 8 (dg >=> lpo) >=>
              final
