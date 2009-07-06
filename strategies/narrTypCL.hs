#!/usr/bin/env runhaskell

import Control.Monad
import Narradar
import Narradar.Types.ArgumentFiltering (typeHeu)
import Strats (pSolver)

main = narradarMain prologSolver

prologSolver opts txt = do
  (typ,pl)  <- parseProlog txt
  prologSolverC opts (typeHeu typ) pl

prologSolverC opts h2 = Strats.pSolver opts (prologP_labelling_all ["bddbddb.jar"] >=> usableSCCsProcessor >=> narrowingSolverC h2)
narrowingSolverC heu  = (msum.uGroundRhsAllP heu >=> aproveSrvP 15)
