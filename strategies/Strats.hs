{-# LANGUAGE NoMonomorphismRestriction, RecordWildCards #-}
module Strats where

import Data.Foldable (toList)
import Data.Maybe
import Prelude as P
import Narradar hiding (refineNarrowing, refineNarrowing', reducingP, pSolver)
import Narradar.Proof

pSolver _ solver p = P.return (maybe False (const True) sol, fromMaybe iprob sol, "") where
    prob  = solver p
    iprob = improve prob
    sol  = runProof' iprob `asTypeOf` Just iprob

pSolver' _ solver p = P.return (maybe False (const True) sol, fromMaybe iprob sol, "") where
    prob  = solver p `asTypeOf` (join $ Pure $ solver p)
    iprob = {-improve-} prob
    sol  = runProof' iprob `asTypeOf` Just iprob

prologSolverOne opts h1 h2 = pSolver' opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2)
prologSolverAll opts h1 h2 = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverAll h2)
prologSolverInf opts h1    = pSolver opts (prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverInf)

narrowingSolverOne heu = refineBy 0 (stage . solve' (reductionPair heu 20 >=> sccProcessor))
                                     refineNarrowingPar

narrowingSolverOne' heu = solveB 4 (solve (reductionPair heu 20 >=> sccProcessor) <|>
                                      refineNarrowing)

narrowingSolverAll heu = refineBy 4 ((uGroundRhsAllP heu >=> aproveSrvP 15))
                                    refineNarrowing

narrowingSolverInf = refineBy 4 (safeAFP >=> aproveSrvP defaultTimeout)
                                  refineNarrowing

refineNarrowing p
  | length (rules $ dps p) > 1
  = (firstP [ msum . instantiation
            , msum . finstantiation
            , msum . narrowing ]
     >=> sccProcessor) p
  | otherwise = (msum . narrowing >=> sccProcessor) p

refineNarrowingPar p
  | length (rules $ dps p) > 1
  = (firstP [ msumPar . instantiation
            , msumPar . finstantiation
            , msumPar . narrowing ]
     >=> sccProcessor) p
  | otherwise = (msumPar . narrowing >=> sccProcessor) p


reducingP solver p = solver p P.>>= \p' -> guard (length (rules p') <= length (rules p)) P.>> P.return p'
{-
refineBy' maxDepth f refiner x = f x `mplus` loop maxDepth x where
  loop 0 x = refiner x >>= f
  loop i x = refiner x >>= \x' ->
               if or [ length(pairs x') <= length(pairs x)
                     , length (rr x') < length (rr x)]
                  then f x' `mplus` loop (i-1) x'
                  else loop (i-1) x'
   where pairs = rules . dps
         rr p  = let p' = head (toList $ usableRulesP p) in rules (trs p')
-}