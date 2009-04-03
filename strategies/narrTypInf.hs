#!/usr/bin/env runhaskell

import Narradar
import Strats

main = narradarMain solveMain

solveMain opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverInf opts (typeHeu typ) pl


