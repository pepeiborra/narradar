#!/usr/bin/env runhaskell

import Strats
import Narradar


main = narradarMain prologSolver

prologSolver opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverInf opts (simpleHeu outermost) pl
