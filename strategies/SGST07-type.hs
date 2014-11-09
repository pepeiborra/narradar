#!/usr/bin/env runhaskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.DeepSeq
import Control.Monad
import Control.Monad.Stream
import Control.Parallel.Strategies
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost, typeHeu)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.RPO
import Narradar.Processor.RPO.Yices
import Narradar.Processor.LOPSTR09
import Narradar.Framework.GraphViz
import Lattice
import Narradar.Utils (pprTrace)

instance IsMZero Stream where
  isMZero = null . runStream

--import Narradar.Utils

main = narradarMain listToMaybe

-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getProblemType p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"

-- Prolog
instance Dispatch PrologProblem where
  dispatch p = do
      let typ = inferType p
      let strat = apply (SKTransformInfinitary (typeHeu typ)) >=>
                  depGraph >=>
                  apply (InfinitaryToRewriting (typeHeu typ) True) >=>
                  dispatch
      strat p

-- Rewriting
instance (Pretty (DPIdentifier id), Ord id, HasTrie id) => Dispatch (NProblem Rewriting (DPIdentifier id)) where
  dispatch = sc >=> rpoPlusTransforms >=> final

instance (id ~ DPIdentifier a, Pretty id, HasTrie a, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = sc >=> rpoPlusTransformsPar >=> final

-- Infinitary
instance (id  ~ DPIdentifier a, Ord a, HasTrie a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) Rewriting) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply DependencyGraphSCC >=>
                 apply (InfinitaryToRewriting bestHeu True) >=>
                 dispatch)

instance (id  ~ DPIdentifier a, Ord a, HasTrie a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) IRewriting) (DPIdentifier a)) where
  dispatch = mkDispatcher
                (apply DependencyGraphSCC >=>
                 apply (InfinitaryToRewriting bestHeu True) >=>
                 dispatch)

-- ----------------------------

sc = apply DependencyGraphSCC >=> try(apply SubtermCriterion)

rpoPlusTransforms
   = depGraph >=>
     repeatSolver 3 ( (lpo .|. rpo .|. graphTransform) >=> depGraph)
  where
    lpo  = apply (RPOProc LPOAF  SMTFFI)
    rpo  = apply (RPOProc RPOSAF SMTFFI)


rpoPlusTransformsPar = parallelize f where
 f = depGraph >=>
     repeatSolver 5 ( (lpo .||. rpo .||. graphTransform) >=> depGraph)
  where
    lpo = apply (RPOProc LPOAF (SMTSerial 60))
    rpo = apply (RPOProc RPOSAF (SMTSerial 60))


graphTransform = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
