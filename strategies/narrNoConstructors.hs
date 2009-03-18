#!/usr/bin/env runhaskell

{-# LANGUAGE NoMonomorphismRestriction #-}
import Prelude hiding (Monad(..))

import Narradar
import Narradar.ArgumentFiltering

main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolver' (simpleHeu' $ \p -> Heuristic (predHeuOne allInner (noConstructors (getSignature p))) False) (typeHeu typ) pl

prologSolver' h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolver h2

narrowingSolver heu = uGroundRhsAllP heu >=> aproveSrvP defaultTimeout
