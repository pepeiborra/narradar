#!/usr/bin/env runhaskell
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}

import Prelude hiding (Monad(..))

import Narradar
import Narradar.Solver hiding (prologSolver, prologSolver')
import Narradar.ArgumentFiltering as AF
import Data.Foldable


main = narradarMain prologSolver

prologSolver txt = do
  (typ,pl)  <- parseProlog txt
  prologSolver' noU1sHeu (typeHeu typ) pl

prologSolver' h1 h2 = prologP_labelling_sk h1 >=> usableSCCsProcessor >=> narrowingSolverOne h2

narrowingSolverOne heu = solve (reductionPair heu 20 >=> sccProcessor)

refineNarrowing = instantiation <|> finstantiation <|> narrowing

-- No U1s Heuristic
-- ----------------
noU1sHeu = MkHeu (IsU1 . getSignature)

data IsU1 id (f :: * -> *) = IsU1 (Signature id)
instance (T id :<: f, IsU1Id id, Ord id, Foldable f) => PolyHeuristic IsU1 id f where
  runPolyHeu (IsU1 sig) =  Heuristic (predHeuOne allOuter noU1s `AF.or` predHeuOne allOuter (noConstructors sig)) False
    where noU1s _af (t, 1) = not$ isU1Id t
          noU1s _ _ = True

class IsU1Id id where isU1Id :: id -> Bool
instance IsU1Id PId where isU1Id (symbol -> UId{}) = True; isU1Id _ = False
instance IsU1Id PS  where isU1Id (UId{}) = True; isU1Id _ = False
instance IsU1Id LPS where isU1Id (unlabel -> UId{}) = True; isU1Id _ = False
instance IsU1Id LPId where isU1Id (unlabel.symbol -> UId{}) = True; isU1Id _ = False
