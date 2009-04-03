#!/usr/bin/env runhaskell

import Narradar
import Narradar.Proof
import Strats

main = narradarMain prologSolver

prologSolver opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverAll opts (typeHeu2 typ) (typeHeu typ) pl
