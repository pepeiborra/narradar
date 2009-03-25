{-# LANGUAGE NoMonomorphismRestriction, RecordWildCards #-}
module Strats where

import Data.Maybe
import Prelude as P
import Narradar hiding (refineNarrowing, refineNarrowing', reducingP, pSolver)
import Narradar.Proof

prologSolverOne opts h1 h2 = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2)
{-
pSolver Options{..} solver p = do
  (b,sol,log) <- runAndPruneProofT (verbose>0) (solver p)
  sol' <- unwrap sol
  P.return (b,sol',log)
-}
pSolver _ solver p = P.return (maybe False (const True) sol, fromMaybe prob sol, "") where
    prob = solver p
    (sol) = runProof prob

prologSolverAll opts h1 h2 = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverAll h2)

prologSolverInf opts  h1 = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverInf)

narrowingSolverOne heu = refineBy 30 (solve (reductionPair heu 20 >=> sccProcessor))
                                     refineNarrowing

narrowingSolverOne' heu = solveB 12 (solve (reductionPair heu 20 >=> sccProcessor) <|>
                                      refineNarrowing)

narrowingSolverAll heu = refineBy 12 ((uGroundRhsAllP heu >=> aproveSrvP 15))
                                    refineNarrowing

narrowingSolverInf = refineBy 1 (safeAFP >=> aproveSrvP defaultTimeout)
                                    refineNarrowing


refineNarrowing = firstP [ msum . instantiation
                         , msum . finstantiation
                         , msum . narrowing ]
                  >=> sccProcessor

refineNarrowingPar = firstP [ msumPar . instantiation
                         , msumPar . finstantiation
                         , msumPar . narrowing ]
                  >=> sccProcessor


reducingP solver p = solver p P.>>= \p' -> guard (length (rules p') <= length (rules p)) P.>> P.return p'