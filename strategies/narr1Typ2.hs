#!/usr/bin/env runhaskell

import Narradar
import Narradar.Proof
import Strats

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne opts (typeHeu2 typ) (typeHeu typ) pl