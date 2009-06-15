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
  prologSolverAll opts noOutsHeu (typeHeu typ) pl




-- No U1s Heuristic
-- ----------------
noOutsHeu = MkHeu (NoOuts . getSignature)

data NoOuts id (f :: * -> *) = NoOuts (Signature id)
instance (IsPrologId id, Ord id, HasId f id, Foldable f) => PolyHeuristic NoOuts id f where
  runPolyHeu (NoOuts sig) =
      Heuristic (predHeuOne allOuter noOuts `AF.or`
                 predHeuOne allOuter (noConstructors sig))
                False
    where noOuts _af (t, 1) = not (isOutId t) && not (isUId t)
          noOuts _af (t, _) = not (isOutId t)
