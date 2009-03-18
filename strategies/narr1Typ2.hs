#!/usr/bin/env runhaskell

import Narradar

main = narradarMain $ \input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne (typeHeu2 typ) (typeHeu typ) pl

prologSolverOne h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2

narrowingSolverOne heu = solveB 3 ((trivialNonTerm >=> reductionPair heu 20 >=> sccProcessor) <|>
                                   (refineNarrowing >=> sccProcessor))
 where
  refineNarrowing = (finstantiation <|> narrowing <|> instantiation)
