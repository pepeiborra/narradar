#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain $ \input -> do
  (typ,pl)  <- parseProlog input
  prologSolverAll (simpleHeu outermost) (typeHeu typ) pl
