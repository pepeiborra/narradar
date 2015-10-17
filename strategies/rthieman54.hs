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
import Narradar.Processor.RPO
import Narradar.Processor.RPO.YicesPipe
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
             >=> lfp dgi >=> inst >=> dg >=> try ur >=> rew >=> dg >=> sc >=> dg
             >=> final
    where
      dgi = inn `orElse` ur `orElse` dg
      inn    = apply ToInnermost
