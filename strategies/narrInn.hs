#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain $ \input -> do
  (typ,pl)  <- parseProlog input
  prologSolverAll (simpleHeu innermost) (typeHeu typ) pl
