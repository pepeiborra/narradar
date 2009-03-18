#!/usr/bin/env runhaskell


import Narradar

main = narradarMain $ \input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne (simpleHeu outermost) (typeHeu typ) pl


prologSolverOne h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2

narrowingSolverOne heu = solveB 2 ((trivialNonTerm >=> reductionPair heu 20 >=> sccProcessor) <|>
                                   (refineNarrowing >=> sccProcessor))
 where
  refineNarrowing = (finstantiation <|> narrowing <|> instantiation)
