#!/usr/bin/env runhaskell

{-# LANGUAGE NoImplicitPrelude #-}
import Prelude hiding (Monad(..))

import Narradar

main = narradarMain (parseProlog >=> prologSolver)

prologSolver    = prologSolver' (\typ _ -> typeHeu2 typ) (aproveSrvP defaultTimeout)
prologSolver' heu k = (prologP_labelling_sk heu >=> narrowingSolverUc >=> k)

narrowingSolverUc = usableSCCsProcessor >=> cycleProcessor >=> iUsableProcessor >=> groundRhsOneP
