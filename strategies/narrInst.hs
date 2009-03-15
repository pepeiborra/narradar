#!/usr/bin/env runhaskell

{-# LANGUAGE NoImplicitPrelude #-}
import Prelude hiding (Monad(..))

import Narradar

main = narradarMain (parseProlog >=> prologSolver)

prologSolver    = prologSolver' (\typ _ -> typeHeu2 typ) (aproveSrvP defaultTimeout)
prologSolver' heu k = (prologP_labelling_sk heu >=> narrowingSolverUScc >=> k)


narrowingSolverUScc =usableSCCsProcessor >=>  refineNarrowing >=>  refineNarrowing >=>  refineNarrowing >=>  iUsableProcessor >=> groundRhsAllP

refineNarrowing = instantiation .|. finstantiation .|. narrowing