#!/usr/bin/env runhaskell

import Narradar
import Strats
import Narradar.ArgumentFiltering

main = narradarMain prologSolver

prologSolver opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverAll opts (simpleHeu' $ \p -> Heuristic (predHeuOne allInner (noConstructors (getSignature p))) False) 
                  (typeHeu typ)
                  pl
