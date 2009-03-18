#!/usr/bin/env runhaskell

import Prelude hiding (Monad(..))
import Narradar

main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolver' (typeHeu typ) (typeHeu typ) pl

prologSolver' h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> uGroundRhsAllP h2 >=> aproveSrvP defaultTimeout
