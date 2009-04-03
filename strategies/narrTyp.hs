#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain prologSolver

prologSolver opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverAll opts (typeHeu typ) (typeHeu typ) pl

