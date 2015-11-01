{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveFunctor, DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Narradar.Constraints.SAT.Usable where

import           Control.DeepSeq
import           Control.Monad.Reader (MonadReader)
import           Data.Hashable
import qualified Data.Term             as Family
import           Data.Typeable
import           Debug.Hoed.Observe
import           Funsat.ECircuit (CastCo, CastCircuit)
import           Funsat.TermCircuit (Co)
import           Funsat.TermCircuit.SomeCircuit
import           Funsat.TermCircuit.WPO (WPOSymbol(..))
import           Funsat.TermCircuit.Ext
import           Funsat.TermCircuit.Symbols hiding (Var)

import           Narradar.Constraints.SAT.MonadSAT
import           Narradar.Framework.Ppr            as Ppr
import           Narradar.Types      (DPSymbol(..), GenSymbol(..), RemovePrologId(..), HasArity(..))

-- ------------------------------------------
-- A function for constructing a SAT Symbol
-- -----------------------------------------

data MkSATSymbol env sid = MkSATSymbol {
  mkSatSymbol
     :: forall v id m repr.
        (v  ~ Family.Var sid
        ,id ~ Family.Id sid
        ,Decode v Bool, Show id
        ,Co repr v
        ,MonadSAT repr v m
        ,MonadReader (env repr v) m ) =>
        (id, Int) -> m (sid, [(String, repr v)]) }

-- An implementation of MkSATSymbol
makeUsableSymbol :: ( MonadSAT repr v m
                    , Co repr v
                    , v ~ Family.Var s
                    , Decode s (SymbolRes s)
                    , Show (Family.Id s)
                    , Show s
                    ) => SymbolFactory s m repr
                       -> (Family.Id s, Int)
                       -> m (Usable s, [(String, repr v)])
makeUsableSymbol makeSymbol x = do
  encodeUsable <- boolean_ ("usable_" ++ show(fst x))
  (s, constraints) <- makeSymbol boolean_ natural_ x
  let evalres = mkUsableSymbolDecoder encodeUsable (decode s)
  return (Usable s encodeUsable evalres, constraints)

decodeUsable :: Usable s -> EvalM (Family.Var s) (UsableRes s)
decodeUsable = decode

-- ------------------------------------
-- Symbol classes for AF + Usable rules
-- ------------------------------------

type family SymbolRes a

class UsableSymbol a where
  usable :: a -> Family.Var a

iusable = input . usable

data Usable s = Usable { usableSymbol :: s
                       , encodeUsable :: (Family.Var s)
                       , decodeUsableSymbol :: EvalM (Family.Var s) (UsableRes s)}
                deriving (Generic, Typeable)


type instance Family.Var (Usable s) = Family.Var s
type instance Family.Id  (Usable s) = Family.Id s

deriving instance (Show s, Show(Family.Var s)) => Show (Usable s)

instance HasArity a => HasArity (Usable a) where getIdArity = getIdArity . usableSymbol
instance HasPrecedence s => HasPrecedence (Usable s) where precedence_v = precedence_v . usableSymbol
instance HasFiltering s => HasFiltering (Usable s) where filtering_vv = filtering_vv . usableSymbol
instance IsSimple s => IsSimple(Usable s) where isSimple_v = isSimple_v . usableSymbol
instance HasStatus s => HasStatus (Usable s) where lexPerm_vv = lexPerm_vv . usableSymbol
instance HasLexMul s => HasLexMul(Usable s) where useMul_v = useMul_v . usableSymbol
instance Eq s => Eq (Usable s) where a == b = usableSymbol a == usableSymbol b
instance Ord s => Ord (Usable s) where compare a b = compare (usableSymbol a) (usableSymbol b)
instance Pretty s => Pretty (Usable s) where pPrint = pPrint . usableSymbol
instance Hashable s => Hashable(Usable s) where hashWithSalt s = hashWithSalt s . usableSymbol
instance DPSymbol s => DPSymbol(Usable s) where
  markDPSymbol me = me{usableSymbol = markDPSymbol (usableSymbol me)}
  unmarkDPSymbol me = me{usableSymbol = unmarkDPSymbol (usableSymbol me)}
  isDPSymbol me = isDPSymbol(usableSymbol me)
instance (Var ~ Family.Var s, GenSymbol s, Decode s (SymbolRes s)) => GenSymbol (Usable s) where
  genSymbol = let s :: s = genSymbol in Usable s (V Nothing 14) (mkUsableSymbolDecoder (V Nothing 14) (decode s))
instance Ord a => RemovePrologId (Usable a) where
  type WithoutPrologId (Usable a) = Usable a
  removePrologId = Just

instance Observable1 Usable         where observer1 = observeOpaque "usable-symbol"
instance Observable a => Observable (Usable       a) where observer = observer1 ; observers = observers1

instance UsableSymbol (Usable s) where usable = encodeUsable

instance (NFData a, NFData (Family.Var a)
         ) => NFData(Usable a) where rnf (Usable u enc dec) = rnf u `seq` rnf enc `seq` dec `seq` ()

instance WPOSymbol id => WPOSymbol (Usable id) where
  getW = getW . usableSymbol
  getC = getC . usableSymbol
  getP = getP . usableSymbol
  getAlg = getAlg . usableSymbol
  isTop  = isTop . usableSymbol
  
data UsableRes a = UsableRes { isUsable :: Bool
                             , symbolRes :: SymbolRes a }

deriving instance Eq(SymbolRes a) => Eq(UsableRes a)
deriving instance Ord(SymbolRes a) => Ord(UsableRes a)
deriving instance Show(SymbolRes a) => Show(UsableRes a)
instance Pretty (SymbolRes s) => Pretty (UsableRes s) where pPrint = pPrint . symbolRes

instance () => Decode (Usable s) (UsableRes s) where decode = decodeUsableSymbol

mkUsableSymbolDecoder :: (Show v, Ord v
                         ) => v -> EvalM v (SymbolRes a) -> EvalM v (UsableRes a)
mkUsableSymbolDecoder usable_b evalres = do
  isUsable <- evalB (input usable_b)
  res <- evalres
  return UsableRes { isUsable = isUsable, symbolRes = res }
