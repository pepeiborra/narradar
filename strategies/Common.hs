{-# LANGUAGE NoMonomorphismRestriction #-}

module Common where

import Control.Monad
import Narradar
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
lpo  = apply (RPOProc LPOAF  Needed SMTFFI True)
mpo  = apply (RPOProc MPOAF  Needed SMTFFI True)
lpos = apply (RPOProc LPOSAF Needed SMTFFI True)
rpo  = apply (RPOProc RPOAF  Needed SMTFFI True)
rpos = apply (RPOProc RPOSAF Needed SMTFFI True)
lpoO p = gdmobservers "lpo" applyO (RPOProc LPOAF  Needed SMTFFI True) p


rpoPlus transform
   = repeatSolver 1 ((lpoO .|. rpos .|. transform) >=> dg)

rpoPlusPar transform = parallelize f where
 f = repeatSolver 5 ( (lpo.||. rpos .||. transform) >=> dg)
  where
    lpo  = apply (RPOProc LPOAF  Needed SMTSerial True)
    rpos = apply (RPOProc RPOSAF Needed SMTSerial True)

gt1 = rewO `orElse` (narr .||. finst .||. inst)
gt2 = narr .||. finst .||. inst
