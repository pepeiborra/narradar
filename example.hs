#!/usr/bin/env runhaskell

import Control.Monad
import Narradar
import Narradar.Solver

main = narradarMain (parseProlog >=> prologSolver)