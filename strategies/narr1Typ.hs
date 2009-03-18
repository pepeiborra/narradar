#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain $ \input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne (typeHeu typ) (typeHeu typ) pl
