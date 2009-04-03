#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain prologSolver

prologSolver opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverInf opts (typeHeu2 typ) pl
