module Strats where

import Narradar hiding (refineNarrowing, refineNarrowing')

prologSolverOne h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2

prologSolverAll h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverAll h2

prologSolverInf h1    = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverInf

narrowingSolverOne heu = refineBy 1 (solve (reductionPair heu 20 >=> sccProcessor))
                                    (refineNarrowing' >=> sccProcessor)

narrowingSolverOne' heu = solveB 3 (solve (reductionPair heu 20 >=> sccProcessor) <|>
                                   (refineNarrowing >=> sccProcessor))

narrowingSolverAll heu = refineBy 3 ((uGroundRhsAllP heu >=> aproveSrvP defaultTimeout))
                                    (refineNarrowing >=> sccProcessor)

narrowingSolverInf = refineBy 3 (safeAFP >=> aproveSrvP defaultTimeout)
                                    (refineNarrowing >=> sccProcessor)


refineNarrowing = instantiation <|> finstantiation <|> narrowing
refineNarrowing' = firstP [reducingP (narrowing >=> sccProcessor)
                          ,reducingP (finstantiation >=> sccProcessor)
                          ,reducingP (instantiation >=> sccProcessor)]
