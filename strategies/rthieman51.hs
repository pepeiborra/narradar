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
import Control.Monad ((>=>))
import Data.List (nub)
import Data.Maybe
import Data.Traversable (Traversable)
import Data.Typeable
import Narradar
import Narradar.Processor.WPO.SBV
import Narradar.Processor.RPO.SBV
import Narradar.Processor.RPO
import Common
import Debug.Hoed.Observe

main = commonMain

-- Rewriting
instance () => Dispatch (NProblem Rewriting Id) where
  dispatch = apply RewritingToQRewriting >=> dispatch
instance () => Dispatch (NProblem IRewriting Id) where
  dispatch p = apply RewritingToQRewriting p >>= dispatch

-- QRewriting
instance () => Dispatch (NProblem (QRewritingN Id) Id) where
  dispatch = ev
             >=> lfp dgi >=> ((inst >=> dg >=> rew >=> dg >=> sc >=> dg) `orElse`
                              (finst >=> lfp dgi >=> (lpo .|. narrP [[1]]) >=> lfp dgi >=> narrP [[2]] >=> lfp dgi >=> (rew .|. narrP [[3]]) >=> lfp dgi >=> try ur >=> (mpol (Just 0) (Just 10) ) >=> lfp dgi))
             >=> final
    where
      dgi = inn `orElse` ur `orElse` dg
      inn    = apply ToInnermost
