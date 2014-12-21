{-# LANGUAGE NoMonomorphismRestriction #-}

module Common where

import Control.Monad
import Narradar
import Narradar.Processor.RPO
import Narradar.Processor.WPO
import Debug.Hoed.Observe

-- Solvers
dg  = apply DependencyGraphSCC{useInverse=False}
dgI = apply DependencyGraphSCC{useInverse=True}


sc = apply SubtermCriterion
dgsc = lfp(dg >=> sc)
ev    = apply ExtraVarsP
evO p = gdmobservers "extra vars" applyO ExtraVarsP p
inn = apply ToInnermost >=> dispatch
ur    = apply UsableRules
narr = apply (NarrowingP Nothing)
narrP p x = apply (NarrowingP (Just p)) x
inst  = apply Instantiation
rew   = apply RewritingP
finst = apply FInstantiation
scO p = gdmobservers "Subterm criterion" applyO SubtermCriterion p
urO p = gdmobservers "Usable Rules" applyO UsableRules p
instO p = gdmobservers "Instantiation" applyO Instantiation p
rewO p = gdmobservers "Rewriting" applyO RewritingP p
narrO = gdmobservers "Narrowing" applyO (NarrowingP Nothing)
dgO p = gdmobservers "Graph" applyO (DependencyGraphSCC False) p
lpo  = apply (RPOProc LPOAF  Needed True)
mpo  = apply (RPOProc MPOAF  Needed True)
lpos = apply (RPOProc LPOSAF Needed True)
rpo  = apply (RPOProc RPOAF  Needed True)
rpos = apply (RPOProc RPOSAF Needed True)
lpoO p = gdmobservers "lpo" applyO (RPOProc LPOAF Needed True) p

pol = apply (WPOProc POL Usable)

rpoPlus transform
   = repeatSolver 1 ((lpoO .|. rpos .|. transform) >=> dg)

rpoPlusPar transform = parallelize f where
 f = repeatSolver 5 ( (lpo.||. rpos .||. transform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed True)
    rpos = apply (RPOProc RPOSAF Needed True)

gt1 = rewO `orElse` (narr .||. finst .||. inst)
gt2 = narr .||. finst .||. inst
