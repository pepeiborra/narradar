#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne opts (typeHeu typ) (typeHeu typ) pl
