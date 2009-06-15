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

main = narradarMain $ \opts input -> do
  (typ,pl)  <- parseProlog input
  prologSolverAll opts noU1sHeu (typeHeu typ) pl




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
