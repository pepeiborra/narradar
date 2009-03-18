#!/usr/bin/env runhaskell

import Narradar
import Narradar.ArgumentFiltering
import Strats

main = narradarMain $ \input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne (simpleHeu' $ \p -> Heuristic (predHeuOne allInner (noConstructors (getSignature p))) False)
                  (typeHeu typ)
                  pl

