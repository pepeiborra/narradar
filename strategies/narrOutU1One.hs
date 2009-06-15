#!/usr/bin/env runhaskell
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}

import Data.Foldable
import Narradar
import Narradar.ArgumentFiltering as AF
import Strats

import qualified Data.Set as Set

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverOne opts noU1sHeu innerHeu pl

-- No U1s Heuristic
-- ----------------
innerHeu = simpleHeu $ Heuristic (((Set.fromList.).) . allInner) False

-- No U1s Heuristic
-- ----------------
noU1sHeu = MkHeu (IsU1 . getSignature)

data IsU1 id (f :: * -> *) = IsU1 (Signature id)
instance (IsPrologId id, Ord id, HasId f id, Foldable f) => PolyHeuristic IsU1 id f where
  runPolyHeu (IsU1 sig) =
      Heuristic (predHeuOne allOuter noU1s `AF.or`
                 predHeuOne allOuter (noConstructors sig))
                False
    where noU1s _af (t, 1) = not$ isUId t
          noU1s _ _ = True
