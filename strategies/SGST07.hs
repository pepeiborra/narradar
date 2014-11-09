{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE CPP #-}


--module SGST07 where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Stream
import Control.Parallel.Strategies
import Data.Maybe
import qualified Language.Prolog.Syntax as Prolog
import MuTerm.Framework.Proof (parAnds)
import Narradar
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, typeHeu, innermost)
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.NarrowingGen
import Narradar.Processor.RPO
import Narradar.Processor.RPO.Yices
import Narradar.Processor.LOPSTR09
import Narradar.Processor.InfinitaryProblem
import Narradar.Framework.GraphViz
import Lattice
import Narradar.Utils (pprTrace)


import Narradar.Interface.Cli
main = narradarMain listToMaybe


-- Missing dispatcher cases
instance (IsProblem typ, Pretty typ) => Dispatch (Problem typ trs) where
    dispatch p = error ("missing dispatcher for problem of type " ++ show (pPrint $ getFramework p))

instance Dispatch thing where dispatch _ = error "missing dispatcher"

-- Prolog
instance Dispatch PrologProblem where
  dispatch p = do
      let typ = inferType p
      let strat = apply (SKTransformInfinitary (typeHeu typ)) >=>
                  dg >=>
                  apply (InfinitaryToRewriting (typeHeu typ) True) >=>
                  dispatch
      strat p

-- Rewriting
instance (Pretty (DPIdentifier id), Ord id, HasTrie id) => Dispatch (NProblem Rewriting (DPIdentifier id)) where
  dispatch = ev >=> (inn .|. (dg >=> rpoPlusTransforms >=> final))
--  dispatch = mkDispatcher (depGraph >=> apply (RPOProc LPOAF (Yices 60)) >=> depGraph)

instance (id ~ DPIdentifier a, Pretty id, HasTrie a, Ord a) => Dispatch (NProblem IRewriting id) where
  dispatch = ev >=> rpoPlusTransforms >=> final

{-
-- Narrowing Goal
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, HasTrie id) => Dispatch (NProblem (NarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply (NarrowingGoalToInfinitary bestHeu True) >=> dispatch
instance (Pretty (DPIdentifier id), Pretty (GenId id), Ord id, HasTrie id) => Dispatch (NProblem (CNarrowingGoal (DPIdentifier id)) (DPIdentifier id)) where
  dispatch = apply (NarrowingGoalToInfinitary bestHeu True) >=> dispatch
-}

-- Infinitary
instance (id  ~ DPIdentifier a, Ord a, HasTrie a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) Rewriting) (DPIdentifier a)) where
  dispatch = dg >=>
             apply (InfinitaryToRewriting bestHeu True) >=>
             dispatch

instance (id  ~ DPIdentifier a, Ord a, HasTrie a, Lattice (AF_ id), Pretty id) =>
           Dispatch (NProblem (Infinitary (DPIdentifier a) IRewriting) (DPIdentifier a)) where
  dispatch = dg >=>
             apply (InfinitaryToRewriting bestHeu True) >=>
             dispatch

-- ----------------------------

sc  = apply SubtermCriterion
inn = apply ToInnermost >=> dispatch
dg  = apply DependencyGraphSCC{useInverse=True}
ev  = apply ExtraVarsP

rpoPlusTransforms
   = repeatSolver 10 ( (sc .|. lpo .|. rpos .|. graphTransform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTFFI)
    lpos = apply (RPOProc LPOSAF Needed SMTFFI)
    rpos = apply (RPOProc RPOSAF Needed SMTFFI)


rpoPlusTransformsPar = parallelize f where
 f = repeatSolver 5 ( (lpo .||. rpo .||. graphTransform) >=> dg)
  where
    lpo = apply (RPOProc LPOAF  Needed SMTSerial)
    rpo = apply (RPOProc RPOSAF Needed SMTSerial)


graphTransform = apply NarrowingP .||. apply FInstantiation .||. apply Instantiation
