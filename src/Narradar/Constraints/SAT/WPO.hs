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
{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}

module Narradar.Constraints.SAT.WPO where

import           Control.Monad.Reader              (MonadReader(..))
import           Data.Hashable
import qualified Data.Term                         as Family
import           Funsat.ECircuit                   (Natural, MaxCircuit)
import           Funsat.TermCircuit                (Co)
import           Funsat.TermCircuit.Symbols        (SymbolFactory)
import           Funsat.TermCircuit.WPO (WPOCircuit, WPOAlgebra(..))
import           Funsat.TermCircuit.WPO.POL        (POL(POL))
import qualified Funsat.TermCircuit.WPO.POL        as POL
import           Funsat.TermCircuit.WPO.SUM        (SUM(SUM), SUMOptions(SUMOptions))
import qualified Funsat.TermCircuit.WPO.SUM        as SUM
import           Funsat.TermCircuit.WPO.MAX        (MAX(MAX))
import qualified Funsat.TermCircuit.WPO.MAX        as MAX
import           Funsat.TermCircuit.WPO.MPOL        (MPOL(MPOL))
import qualified Funsat.TermCircuit.WPO.MPOL        as MPOL
import           Funsat.TermCircuit.WPO.Symbols    (WPOSymbolBase(Symbol, theSymbol)
                                                   ,WPOOptions(..), wpoOptions
                                                   ,WPORange(..), WPOStatus(..))
import qualified Funsat.TermCircuit.WPO.Symbols    as WPO

import           Narradar.Constraints.SAT.MonadSAT
import           Narradar.Constraints.SAT.Usable   hiding (makeUsableSymbol)
import           Narradar.Types                    (DPSymbol(..), HasArity(..), GenSymbol(..))

import Debug.Hoed.Observe

-- -----------------------
-- WPO Algebra instances
-- -----------------------

instance (WPOCircuit (repr (Usable (SUM v id)))
         ) => WPOAlgebra (repr (Usable(SUM v id))) where
  aGt = SUM.agt
  aGe = SUM.age


instance (WPOCircuit (repr (Usable (POL v id)))
         ) => WPOAlgebra (repr (Usable(POL v id))) where
  aGt = POL.agt
  aGe = POL.age

instance (WPOCircuit (repr (Usable (MAX v id)))
         ,MaxCircuit (repr (Usable (MAX v id)))
         ) => WPOAlgebra (repr (Usable(MAX v id))) where
  aGt = MAX.agt
  aGe = MAX.age


instance (WPOCircuit  (repr (Usable (MPOL v id)))
         ,MaxCircuit (repr (Usable (MPOL v id)))
         ,ECircuit (repr (Usable (MPOL v id)))
         ) => WPOAlgebra (repr (Usable(MPOL v id))) where
  aGt = MPOL.agt
  aGe = MPOL.age


-- -----------
-- MkSATSymbol
-- -----------

newtype EnvWPO (repr :: * -> *) v = EnvWPO (Natural v)

-- An implementation of MkSATSymbol
makeUsableSymbol :: ( MonadSAT repr v m
                    , MonadReader (EnvWPO repr v) m
                    , Co repr v
                    , v ~ Family.Var s
                    , Decode s (SymbolRes s)
                    , Show (Family.Id s)
                    ) => (Natural v -> SymbolFactory s m repr)
                       -> (Family.Id s, Int)
                       -> m (Usable s, [(String, repr v)])
makeUsableSymbol makeSymbol x = do
  encodeUsable <- boolean_ ("usable_" ++ show x)
  EnvWPO w0    <- ask
  (s, constraints) <- makeSymbol w0 boolean_ natural_ x
  let evalres = mkUsableSymbolDecoder encodeUsable (decode s)
  return (Usable s encodeUsable evalres, constraints)


pol'  :: WPOOptions -> MkSATSymbol EnvWPO (Usable (POL  Var id))
sum'  :: SUMOptions -> MkSATSymbol EnvWPO (Usable (SUM  Var id))
max'  :: WPOOptions -> MkSATSymbol EnvWPO (Usable (MAX  Var id))
mpol' :: WPOOptions -> MkSATSymbol EnvWPO (Usable (MPOL Var id))
pol'  opts = MkSATSymbol (makeUsableSymbol $ POL.pol   opts)
sum'  opts = MkSATSymbol (makeUsableSymbol $ SUM.sum   opts)
max'  opts = MkSATSymbol (makeUsableSymbol $ MAX.max   opts)
mpol' opts = MkSATSymbol (makeUsableSymbol $ MPOL.mpol opts)


-- ----------------------------
-- Monotone Reduction Pairs
-- ----------------------------
polo = pol' $ wpoOptions{ coefficients = Variable (Just 0) Nothing, statusType = Empty }
lpo  = max' $ wpoOptions{ coefficients = Fixed 1, constants = Fixed 0, statusType = Total}
kbo  = pol' $ wpoOptions{ coefficients = Fixed 1, statusType = Total }
tkbo = pol' $ wpoOptions{ coefficients = Variable (Just 0) Nothing, statusType = Total }

-- ----------------------------
-- Non-monotone Reduction Pairs
-- ----------------------------
mpol = mpol' $ wpoOptions{ coefficients = Variable (Just 0) Nothing
                         , constants = Variable (Just 0) Nothing }
msum = mpol' $ wpoOptions{ coefficients = Variable (Just 0) (Just 1)
                         , constants = Variable (Just 0) Nothing}
sum  = sum'  $ SUMOptions Partial
max  = max'  $ wpoOptions{ coefficients = Variable (Just 0) (Just 1)
                         , constants = Variable (Just 0) Nothing
                         , statusType = Empty}
lpoAF  = max'  $ wpoOptions{ coefficients = Fixed 1, constants = Fixed 0}
kboAF  = pol'  $ wpoOptions{ coefficients = Fixed 1 }

-- ----------------------------------
-- Narradar instances for WPO symbols
-- ----------------------------------

type instance SymbolRes (POL  v a) = WPO.SymbolRes a
type instance SymbolRes (SUM  v a) = WPO.SymbolRes a
type instance SymbolRes (MAX  v a) = WPO.SymbolRes a
type instance SymbolRes (MPOL v a) = WPO.SymbolRes a

instance Hashable a => Hashable (POL v a) where hashWithSalt s (POL Symbol{theSymbol=x}) = hashWithSalt s x
instance Hashable a => Hashable (SUM v a) where hashWithSalt s (SUM (POL Symbol{theSymbol=x})) = hashWithSalt s x
instance Hashable a => Hashable (MAX v a) where hashWithSalt s (MAX Symbol{theSymbol=x}) = hashWithSalt s x
instance Hashable a => Hashable (MPOL v a) where hashWithSalt s (MPOL Symbol{theSymbol=x}) = hashWithSalt s x
instance DPSymbol a => DPSymbol (WPOSymbolBase v a) where
  markDPSymbol = fmap markDPSymbol
  unmarkDPSymbol = fmap unmarkDPSymbol
  isDPSymbol = isDPSymbol . theSymbol

deriving instance DPSymbol a => DPSymbol (POL v a)
deriving instance DPSymbol a => DPSymbol (SUM v a)
deriving instance DPSymbol a => DPSymbol (MAX v a)
deriving instance DPSymbol a => DPSymbol (MPOL v a)

instance HasArity a => HasArity (WPOSymbolBase v a) where getIdArity = getIdArity . theSymbol
deriving instance HasArity a => HasArity(POL v a)
deriving instance HasArity a => HasArity(SUM v a)
deriving instance HasArity a => HasArity(MAX v a)
deriving instance HasArity a => HasArity(MPOL v a)

instance Decode (WPOSymbolBase v a) (WPO.SymbolRes a) where decode = WPO.decodeSymbol
instance Decode (POL  v a) (WPO.SymbolRes a) where decode (POL  x) = decode x
instance Decode (SUM  v a) (WPO.SymbolRes a) where decode (SUM  x) = decode x
instance Decode (MAX  v a) (WPO.SymbolRes a) where decode (MAX  x) = decode x
instance Decode (MPOL v a) (WPO.SymbolRes a) where decode (MPOL x) = decode x

instance Observable1 (POL v)  where observer1 = observeOpaque "POL  Symbol"
instance Observable1 (SUM v)  where observer1 = observeOpaque "SUM  Symbol"
instance Observable1 (MAX v)  where observer1 = observeOpaque "MAX  Symbol"
instance Observable1 (MPOL v) where observer1 = observeOpaque "MPOL Symbol"
instance Observable a => Observable (POL v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (SUM v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (MAX v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (MPOL v a) where observer = observer1 ; observers = observers1
