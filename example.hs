#!/usr/bin/env runhaskell

import Control.Monad
import Narradar
import Narradar.Solver

main = narradarMain (parseProlog >=> prologSolver)

-- Our main solving scheme
narradarSolver       = narradarSolver' (aproveSrvP defaultTimeout)
narradarSolver' aproveS p
   | isRewritingProblem    p = aproveS p
   | isAnyNarrowingProblem p = narrowingSolver 3 aproveS p


narrowingSolverUScc = usableSCCsProcessor >=> iUsableProcessor >=> groundRhsAllP

prologSolver_noL        = prologSolver_noL' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver_noL' heu k = prologP_sk heu >=> (return.convert) >=> narrowingSolverUScc >=> k

{-# off SPECIALIZE prologSolver :: Problem BBasicId -> PPT LId BBasicLId Html IO #-}
prologSolver    = prologSolver' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver' heu k = (prologP_labelling_sk heu >=> narrowingSolverUScc >=> k)

prologSolver_one        = prologSolver_one' (\typ _ -> typeHeu typ) (aproveSrvP defaultTimeout)
prologSolver_one' heu k = (prologP_labelling_sk heu >=> usableSCCsProcessor >=> narrowingSolver 1 k)

narrowingSolver 0 _ = const mzeroM
narrowingSolver 1 k = cycleProcessor >=> iUsableProcessor >=> groundRhsOneP >=> k
narrowingSolver depth _ | depth < 0 = error "narrowingSolver: depth must be positive"
narrowingSolver depth k =
       cycleProcessor >=> iUsableProcessor >=>
       ((groundRhsOneP >=> k)
        .|.
        (refineNarrowing >=> narrowingSolver (depth-1) k))

narrowingSolverScc 0 _ = const mzeroM
narrowingSolverScc 1 k = sccProcessor >=> iUsableProcessor >=> groundRhsAllP >=> k
narrowingSolverScc depth _ | depth < 0 = error "narrowingSolverScc: depth must be positive"
narrowingSolverScc depth k =
        sccProcessor >=> iUsableProcessor >=>
       ((groundRhsAllP >=> k)
        .|.
        (refineNarrowing >=> narrowingSolverScc (depth-1) k))

refineNarrowing = instantiation .|. finstantiation .|. narrowing
