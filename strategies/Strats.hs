{-# LANGUAGE NoMonomorphismRestriction, RecordWildCards #-}
module Strats where

import FBackTrack
import Control.Monad.Logic (observeMany)
import Data.Foldable (toList)
import Data.Maybe
import Prelude as P
import Narradar hiding (refineNarrowing, refineNarrowing', reducingP, pSolver)
import Narradar.Proof
{-
pSolver Options{..} solver p = do
  (b,sol,log) <- runAndPruneProofT (verbose>0) (solver p)
  sol' <- unwrap sol
  P.return (b,sol',log)
-}
pSolver _ solver p = P.return (maybe False (const True) sol, fromMaybe prob sol, "") where
    prob = solver p
--    sol  = runProof prob
--    (sol) = listToMaybe $ runM Nothing (runProof prob)
    (sol) = listToMaybe $ observeMany 1 (runProof prob)

prologSolverOne opts h1 h2 = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2)
prologSolverAll opts h1 h2 = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverAll h2)
prologSolverInf opts h1    = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverInf)

narrowingSolverOne heu = refineBy 10 (stage . solve (reductionPair heu 20 >=> sccProcessor))
                                     refineNarrowingPar

narrowingSolverOne' heu = solveB 12 (solve (reductionPair heu 20 >=> sccProcessor) <|>
                                      refineNarrowing)

narrowingSolverAll heu = refineBy 12 ((uGroundRhsAllP heu >=> aproveSrvP 15))
                                    refineNarrowing

narrowingSolverInf = refineBy 12 (safeAFP >=> aproveSrvP defaultTimeout)
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