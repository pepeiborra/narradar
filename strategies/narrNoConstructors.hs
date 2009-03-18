#!/usr/bin/env runhaskell

import Narradar
import Strats
import Narradar.ArgumentFiltering

main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverAll (simpleHeu' $ \p -> Heuristic (predHeuOne allInner (noConstructors (getSignature p))) False) 
                  (typeHeu typ)
                  pl
