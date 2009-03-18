#!/usr/bin/env runhaskell

import Strats
import Narradar


main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverInf (simpleHeu outermost) pl
