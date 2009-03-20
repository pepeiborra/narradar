#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverAll (typeHeu2 typ) (typeHeu typ) pl