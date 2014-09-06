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

module Narradar.Constraints.SAT.RPOAF.Symbols where

import           Control.DeepSeq
import           Data.Hashable
import qualified Data.Term                         as Family
import           Data.Typeable
import           Funsat.Circuit                    (Co)
import           Funsat.RPOCircuit.Symbols         (SymbolRes, SymbolFactory, RPOSsymbol(..), RPOsymbol(..), LPOSsymbol(..), LPOsymbol(..), MPOsymbol(..), Natural)
import qualified Funsat.RPOCircuit.Symbols         as Funsat

import           Narradar.Constraints.SAT.MonadSAT
import           Narradar.Framework.Ppr            as Ppr
import           Narradar.Types                    (DPSymbol(..), HasArity(..), GenSymbol(..))
import           Control.Monad (liftM)

import Debug.Hoed.Observe
import GHC.Generics (Generic)

-- ------------------------------------
-- Symbol classes for AF + Usable rules
-- ------------------------------------

class UsableSymbol a where usable :: a -> Family.Var a

iusable = input . usable

-- -------------------------------------------------
-- Encoding of RPO symbols with usable rules
-- -------------------------------------------------

data Usable s = Usable { usableSymbol :: s
                       , encodeUsable :: (Family.Var s)
                       , decodeUsableSymbol :: EvalM (Family.Var s) (UsableSymbolRes (Family.Id s))}
                deriving (Generic, Typeable)

data UsableSymbolRes a = UsableSymbolRes { isUsable :: Bool
                                         , symbolRes :: SymbolRes a }
                       deriving (Eq, Ord, Show, Generic)

theSymbolR = Funsat.theSymbolR . symbolRes
prec = Funsat.prec . symbolRes
filtering = Funsat.filtering . symbolRes
status = Funsat.status . symbolRes

mkUsableSymbolDecoder :: (Show v, Ord v) => v -> EvalM v (SymbolRes a) -> EvalM v (UsableSymbolRes a)
mkUsableSymbolDecoder usable_b evalres = do
  isUsable <- evalB (input usable_b)
  res <- evalres
  return UsableSymbolRes { isUsable = isUsable, symbolRes = res }

type instance Family.Var (Usable s) = Family.Var s
type instance Family.Id  (Usable s) = Family.Id s

deriving instance (Show s, Show(Family.Var s)) => Show (Usable s)

instance HasPrecedence s => HasPrecedence (Usable s) where precedence_v = precedence_v . usableSymbol
instance HasFiltering s => HasFiltering (Usable s) where listAF_v = listAF_v . usableSymbol ; filtering_vv = filtering_vv . usableSymbol
instance HasStatus s => HasStatus (Usable s) where useMul_v = useMul_v . usableSymbol ; lexPerm_vv = lexPerm_vv . usableSymbol
instance Eq s => Eq (Usable s) where a == b = usableSymbol a == usableSymbol b
instance Ord s => Ord (Usable s) where compare a b = compare (usableSymbol a) (usableSymbol b)
instance Pretty s => Pretty (Usable s) where pPrint = pPrint . usableSymbol
instance Pretty s => Pretty (UsableSymbolRes s) where pPrint = pPrint . symbolRes
instance Hashable s => Hashable(Usable s) where hashWithSalt s = hashWithSalt s . usableSymbol
instance DPSymbol s => DPSymbol(Usable s) where
  markDPSymbol me = me{usableSymbol = markDPSymbol (usableSymbol me)}
  unmarkDPSymbol me = me{usableSymbol = unmarkDPSymbol (usableSymbol me)}
  isDPSymbol me = isDPSymbol(usableSymbol me)

instance UsableSymbol (Usable s) where usable = encodeUsable

instance (NFData a, NFData (Family.Var a)
         ) => NFData(Usable a) where rnf (Usable u enc dec) = rnf u `seq` rnf enc `seq` dec `seq` ()

-- -------------------
-- MkSATSymbol
-- -------------------

data MkSATSymbol sid = MkSATSymbol {
  mkSatSymbol
     :: forall v id m repr.
        (v  ~ Family.Var sid
        ,id ~ Family.Id sid
        ,Decode v Bool, Show id, Co repr v, MonadSAT repr v m) =>
        (id, Int) -> m (sid, [(String, repr v)]) }

makeUsableSymbol :: ( MonadSAT repr v m
                    , v ~ Family.Var s
                    , Decode s (SymbolRes (Family.Id s))
                    ) => ((String -> m v) -> (String -> m (Natural v)) -> t -> m (s, constraints))
                       -> t -> m (Usable s, constraints)
makeUsableSymbol makeSymbol x = do
  encodeUsable <- boolean
  (s, constraints) <- makeSymbol boolean_ natural_ x
  let evalres = mkUsableSymbolDecoder encodeUsable (decode s)
  return (Usable s encodeUsable evalres, constraints)

rpos :: MkSATSymbol (Usable (RPOSsymbol Var id))
rpo  :: MkSATSymbol (Usable (RPOsymbol  Var id))
lpos :: MkSATSymbol (Usable (LPOSsymbol Var id))
lpo  :: MkSATSymbol (Usable (LPOsymbol  Var id))
mpo  :: MkSATSymbol (Usable (MPOsymbol  Var id))
rpos  = MkSATSymbol (makeUsableSymbol Funsat.rpos)
rpo   = MkSATSymbol (makeUsableSymbol Funsat.rpo)
lpos  = MkSATSymbol (makeUsableSymbol Funsat.lpos)
lpo   = MkSATSymbol (makeUsableSymbol Funsat.lpo)
mpo   = MkSATSymbol (makeUsableSymbol Funsat.mpo)

type UsableRPOSsymbol v id = Usable (RPOSsymbol v id)

-- ----------------------------------
-- Narradar instances for RPO symbols
-- ----------------------------------

instance Hashable a => Hashable (RPOSsymbol v a) where hashWithSalt s = hashWithSalt s . theSymbol
deriving instance Hashable a => Hashable (RPOsymbol v a)
deriving instance Hashable a => Hashable (LPOsymbol v a)
deriving instance Hashable a => Hashable (MPOsymbol v a)
deriving instance Hashable a => Hashable (LPOSsymbol v a)

instance DPSymbol a => DPSymbol (RPOSsymbol v a) where
   markDPSymbol   = fmap markDPSymbol
   unmarkDPSymbol = fmap unmarkDPSymbol
   isDPSymbol     = isDPSymbol . theSymbol

deriving instance DPSymbol a => DPSymbol (RPOsymbol v a)
deriving instance DPSymbol a => DPSymbol (LPOsymbol v a)
deriving instance DPSymbol a => DPSymbol (MPOsymbol v a)
deriving instance DPSymbol a => DPSymbol (LPOSsymbol v a)

instance HasArity a => HasArity (RPOSsymbol v a) where getIdArity = getIdArity . theSymbol

deriving instance HasArity a => HasArity (RPOsymbol v a)
deriving instance HasArity a => HasArity (MPOsymbol v a)
deriving instance HasArity a => HasArity (LPOsymbol v a)
deriving instance HasArity a => HasArity (LPOSsymbol v a)

removePerm symbolRes@Funsat.SymbolRes{status=Lex _} = symbolRes{Funsat.status = Lex Nothing}
removePerm symbolRes = symbolRes

instance Decode (RPOSsymbol v a) (SymbolRes a) where decode = decodeSymbol
instance Decode (LPOSsymbol v a) (SymbolRes a) where decode = decode . unLPOS
instance Decode (LPOsymbol v a) (SymbolRes a) where decode = liftM removePerm . decode . unLPO
instance Decode (MPOsymbol v a) (SymbolRes a) where decode = decode . unMPO
instance Decode (RPOsymbol v a) (SymbolRes a) where decode = liftM removePerm . decode . unRPO

instance (id ~ Family.Id s) => Decode (Usable s) (UsableSymbolRes id) where decode = decodeUsableSymbol


-- --------------------------------------
-- Support for Goal-problems identifiers
-- --------------------------------------

instance (Show a, GenSymbol a) => GenSymbol (RPOSsymbol Var a) where
    genSymbol = Symbol{ theSymbol    = genSymbol
                      , encodePrec   = V Nothing 10
                      , encodeAFlist = V Nothing 12
                      , encodeAFpos  = []
                      , encodePerm   = []
                      , encodeUseMset= V Nothing 13
                      , decodeSymbol = Funsat.mkSymbolDecoder genSymbol (Funsat.Natural $ V Nothing 10) (V Nothing 12) [] [] (V Nothing 13)
                      }
    goalSymbol = Symbol{ theSymbol    = genSymbol
                       , encodePrec   = error "RPOAF.Symbol : goalSymbol"
                       , encodeAFlist = error "RPOAF.Symbol : goalSymbol"
                       , encodeAFpos  = error "RPOAF.Symbol : goalSymbol"
                       , encodePerm   = []
                       , encodeUseMset= error "RPOAF.Symbol : goalSymbol"
                       , decodeSymbol = return (Funsat.SymbolRes genSymbol 0 (Lex Nothing) (Right []))
                       }
    isGenSymbol  = isGenSymbol  . theSymbol
    isGoalSymbol = isGoalSymbol . theSymbol

deriving instance (Show a, GenSymbol a) => GenSymbol (LPOsymbol  Var a)
deriving instance (Show a, GenSymbol a) => GenSymbol (LPOSsymbol Var a)
deriving instance (Show a, GenSymbol a) => GenSymbol (MPOsymbol  Var a)
deriving instance (Show a, GenSymbol a) => GenSymbol (RPOsymbol  Var a)

instance (Var ~ Family.Var s, GenSymbol s, Decode s (SymbolRes (Family.Id s))) => GenSymbol (Usable s) where
  genSymbol = let s :: s = genSymbol in Usable s (V Nothing 14) (mkUsableSymbolDecoder (V Nothing 14) (decode s))


instance Observable1 Usable where observer1 = observeOpaque "usable-symbol"
instance Observable1 (RPOSsymbol v) where observer1 = observeOpaque "rpos-symbol"
instance Observable1 (RPOsymbol v)  where observer1 = observeOpaque "rpo-symbol"
instance Observable1 (LPOSsymbol v) where observer1 = observeOpaque "lpos-symbol"
instance Observable1 (LPOsymbol v)  where observer1 = observeOpaque "lpo-symbol"
instance Observable1 (MPOsymbol v)  where observer1 = observeOpaque "mpo-symbol"
