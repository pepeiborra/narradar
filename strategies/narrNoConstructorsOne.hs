#!/usr/bin/env runhaskell

import Narradar
import Narradar.ArgumentFiltering
import Strats

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne opts
                  (simpleHeu' $ \p -> Heuristic (predHeuOne allInner (noConstructors (getSignature p))) False)
                  (typeHeu typ)
                  pl

