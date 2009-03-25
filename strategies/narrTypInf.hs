#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain solveMain

solveMain txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverInf (typeHeu typ) pl


