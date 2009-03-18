#!/usr/bin/env runhaskell

import Prelude hiding (Monad(..))

import Data.Foldable
import Narradar
import Narradar.ArgumentFiltering as AF


main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolver' (simpleHeu outermost) (aproveSrvP defaultTimeout) pl

prologSolver' h1 k = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> infSolverUScc >=> k

narrowingSolverOne heu = solve (reductionPair heu 20 >=> sccProcessor)
infSolverUScc = usableSCCsProcessor >=> iUsableRulesP >=> safeAFP
