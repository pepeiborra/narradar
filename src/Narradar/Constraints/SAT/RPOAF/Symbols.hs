{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module Narradar.Constraints.SAT.RPOAF.Symbols where

import           Data.Hashable
import qualified Funsat.TermCircuit.RPO.Symbols    as Funsat
import           Funsat.TermCircuit.RPO.Symbols    hiding (SymbolRes)

import           Narradar.Constraints.SAT.MonadSAT
import           Narradar.Constraints.SAT.Usable
import           Narradar.Types                    (DPSymbol(..), HasArity(..), GenSymbol(..))
import           Control.Monad (liftM)

import Debug.Hoed.Observe

