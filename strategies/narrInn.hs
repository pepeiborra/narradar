#!/usr/bin/env runhaskell

{-# LANGUAGE NoImplicitPrelude #-}
import Prelude hiding (Monad(..))

import Narradar

main = narradarMain (parseProlog >=> prologSolver)

prologSolver    = prologSolver' (\_ -> simpleHeu innermost) (aproveSrvP defaultTimeout)
prologSolver' heu k = (prologP_labelling_sk heu >=> narrowingSolverUScc >=> k)


narrowingSolverUScc = usableSCCsProcessor >=> uGroundRhsAllP bestHeu
