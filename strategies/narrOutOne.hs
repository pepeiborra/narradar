#!/usr/bin/env runhaskell


import Narradar
import Narradar.ArgumentFiltering
import Strats

import qualified Data.Set as Set

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne opts (simpleHeu outermost) (simpleHeu $ Heuristic (((Set.fromList.).) . allInner) False) pl

