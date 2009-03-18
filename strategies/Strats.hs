module Strats where

import Narradar

prologSolverOne h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2

prologSolverAll h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverAll h2


narrowingSolverOne heu = solveB 1 ((trivialNonTerm >=> reductionPair heu 20 >=> sccProcessor) <|>
                                   (refineNarrowing >=> sccProcessor))
 where
  refineNarrowing = (finstantiation <|> narrowing <|> instantiation)

narrowingSolverAll h = uGroundRhsAllP h >=> aproveSrvP defaultTimeout