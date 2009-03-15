#!/usr/bin/env runhaskell

{-# LANGUAGE NoImplicitPrelude, NoMonomorphismRestriction #-}
import Prelude hiding (Monad(..))

import Narradar
import Narradar.ArgumentFiltering

main = narradarMain (parseProlog >=> prologSolver)

prologSolver    = prologSolver' (\_ -> simpleHeu' $ \p -> Heuristic (predHeuOne allInner (noConstructors (getSignature p))) False)
                                (aproveSrvP defaultTimeout)
prologSolver' heu k = (prologP_labelling_sk heu >=> narrowingSolverUScc >=> k)
narrowingSolverUScc = usableSCCsProcessor >=> uGroundRhsAllP bestHeu
infSolverUScc = usableSCCsProcessor >=> iUsableRulesP >=> safeAFP