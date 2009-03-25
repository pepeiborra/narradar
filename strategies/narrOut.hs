#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverAll opts (simpleHeu outermost) (typeHeu typ) pl
