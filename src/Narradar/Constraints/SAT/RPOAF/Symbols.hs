{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ConstraintKinds #-}


module Narradar.Constraints.SAT.RPOAF.Symbols where

import           Control.Applicative
import qualified Control.Exception                 as CE
import           Control.Monad
import           Control.DeepSeq
import           Control.Monad.Identity
import           Control.Monad.List
import qualified Control.RMonad                    as R
import qualified Data.Array                        as A
import           Data.Foldable                     (Foldable, foldMap, toList)
import           Data.List                         ((\\), transpose, inits, zip4)
import           Data.Maybe
import           Data.Monoid                       ( Monoid(..) )
import           Data.Hashable
import           Data.Typeable
import qualified Data.Map                          as Map
import qualified Data.Set                          as Set
import           Data.Traversable                  (Traversable)
import           Funsat.Circuit                    (Co)
import           Narradar.Framework.Ppr            as Ppr

import           Narradar.Constraints.SAT.MonadSAT
import qualified Narradar.Types                    as Narradar
import           Narradar.Types                    hiding (symbol, fresh, constant, Var)
import           Narradar.Utils                    (fmap2)

import qualified Prelude                           as P
import           Prelude                           hiding (catch, lex, not, and, or, any, all, quot, (>))

-- ------------------------------------
-- Symbol classes for AF + Usable rules
-- ------------------------------------

class UsableSymbol v a | a -> v where usable :: a -> v

iusable = input . usable

-- ----------------------------------------------
-- Symbol type carrying the result of a solution
-- ----------------------------------------------

data SymbolRes a = SymbolRes { theSymbolR:: a
                             , precedence :: Int
                             , isUsable   :: Bool
                             , status     :: Status
                             , filtering  :: Either Int [Int] }
  deriving (Eq, Ord, Show, Typeable)

instance Functor SymbolRes where fmap f SymbolRes{..} = SymbolRes{theSymbolR = f theSymbolR, ..}

instance Pretty a => Pretty (SymbolRes a) where
    pPrint SymbolRes{theSymbolR} = pPrint theSymbolR

instance NFData a => NFData (SymbolRes a) where
  rnf (SymbolRes s p u st af) = rnf s `seq` rnf p `seq` rnf u `seq` rnf st `seq` rnf af

-- -------------------------------------------------
-- Encoding of RPO symbols with AF and usable rules
-- -------------------------------------------------

data RPOSsymbol v a = Symbol { theSymbol    :: a
                             , encodePrec   :: v
                             , encodeUsable :: v
                             , encodeAFlist :: v
                             , encodeAFpos  :: [v]
                             , encodePerm   :: [[v]]
                             , encodeUseMset:: v
                             , decodeSymbol :: EvalM v (SymbolRes a)}
   deriving Show

instance Show (EvalM v a) where show _ = "evalM computation"

instance Pretty a => Pretty (RPOSsymbol v a) where
    pPrint Symbol{theSymbol} = pPrint theSymbol

instance Eq   a => Eq   (RPOSsymbol v a) where
    a@Symbol{} == b@Symbol{} = theSymbol a == theSymbol b

instance Ord a => Ord (RPOSsymbol v a) where
   compare a b = theSymbol a `compare` theSymbol b

instance Functor (RPOSsymbol v) where
    fmap f Symbol{..} = Symbol{theSymbol = f theSymbol,
                               decodeSymbol = fmap2 f decodeSymbol, ..}
instance Foldable (RPOSsymbol v) where foldMap f Symbol{..} = f theSymbol

instance Hashable a => Hashable (RPOSsymbol v a) where hash = hash . theSymbol

instance DPSymbol a => DPSymbol (RPOSsymbol v a) where
   markDPSymbol   = fmap markDPSymbol
   unmarkDPSymbol = fmap unmarkDPSymbol
   isDPSymbol     = isDPSymbol . theSymbol

instance HasArity a => HasArity (RPOSsymbol v a) where getIdArity = getIdArity . theSymbol

instance UsableSymbol v (RPOSsymbol v a) where usable = encodeUsable

instance HasPrecedence v (RPOSsymbol v a) where precedence_v = encodePrec
instance HasStatus     v (RPOSsymbol v a) where
    useMul_v   = encodeUseMset
    lexPerm_vv = Just . encodePerm

instance HasFiltering v (RPOSsymbol v a) where
    listAF_v   = encodeAFlist
    filtering_vv = encodeAFpos

instance Decode (RPOSsymbol v a) (SymbolRes a) v where decode = decodeSymbol


type SymbolFactory s = forall id symb m repr . (Show id, Pretty id, DPSymbol id, MonadSAT repr Var m ) => (id, Int, Bool) -> m (s Var id)

--rpos :: SymbolFactory RPOSsymbol
rpos :: (MonadSAT repr v m, Co repr v, Show id, Decode v Bool v) =>
        (id, Int, Bool) -> m (RPOSsymbol v id)
rpos (x, ar, defined) = do
  n_b      <- natural
  perm_bb  <- replicateM ar (replicateM ar boolean)
  mset     <- boolean
  (list_b:pos_bb) <- case ar of
                       0 -> do {lb <- boolean; assert [input lb]; return [lb]}
                       _ -> replicateM (ar + 1) boolean
  usable_b <- boolean

--  when (P.not defined || isDPSymbol x) $ assert [not $ input usable_b]

  let perm_ee = fmap2 input perm_bb
      pos_ee  = fmap  input pos_bb

  -- Filtering invariant
  assertAll [not(input list_b) --> one pos_ee]

  -- Permutation invariants
  -- -----------------------

  -- There is one or zero arguments considered at the k'th perm position,
  assertAll [ or perm_k --> one perm_k
              | perm_k <- transpose perm_ee]
--  assertAllM [ not p ==> and (not <$> perm_i) | (p, perm_i) <- zip pos_ee perm_ee]
  -- Non filtered arguments are considered at exactly one position in the permutation
  -- Filtered arguments may not be used in the permutation
  assertAll [ ite p (one perm_i) (not $ or perm_i)
                  | (p, perm_i) <- zip pos_ee perm_ee]
  -- All non-filtered arguments are permuted 'to the left'
  assertAll [ or perm_k1 --> or perm_k
                  | (perm_k, perm_k1) <- zip (transpose perm_ee) (tail $transpose perm_ee)]

  return $ Symbol
             { theSymbol    = x
             , encodePrec   = encodeNatural n_b
             , encodeUsable = usable_b
             , encodeAFlist = list_b
             , encodeAFpos  = pos_bb
             , encodePerm   = perm_bb
             , encodeUseMset= mset
             , decodeSymbol = mkSymbolDecoder x n_b usable_b list_b pos_bb perm_bb mset}

mkSymbolDecoder :: (Decode v Bool v, Ord v, Hashable v, Show v, Show id
                   )=> id -> Natural v -> v -> v -> [v] -> [[v]] -> v -> EvalM v (SymbolRes id)
mkSymbolDecoder id n_b usable_b list_b pos_bb perm_bb mset = do
                 n          <- decode n_b
                 isList     <- decode list_b
                 pos        <- decode pos_bb
                 isUsable   <- decode usable_b
                 status     <- decode mset
                 perm_bools <- decode perm_bb
                 let the_positions = [fromInteger i | (i,True) <- zip [1..] pos]
                     statusMsg   = mkStatus status perm_bools
                 return$
                  if P.not isList
                   then CE.assert (length the_positions == 1)
                        (SymbolRes id n isUsable statusMsg (Left $ headS the_positions))
                   else (SymbolRes id n isUsable statusMsg (Right the_positions))
  where
   headS [] = error ("mkSymbolDecoder: invalid null collapsing AF for  (" ++ show id ++ ")")
   headS (x:_) = x

-- --------
-- Variants
-- --------

-- LPO with status

newtype LPOSsymbol v a = LPOS{unLPOS::RPOSsymbol v a}
    deriving (Eq, Ord, Show, Hashable, HasArity
             ,HasPrecedence v, HasStatus v, HasFiltering v
             ,UsableSymbol v, DPSymbol, Functor, Foldable)

instance Decode (LPOSsymbol v a) (SymbolRes a) v where decode = decode . unLPOS

--lpo :: SymbolFactory LPOsymbol
lpos x = do
  s <- rpos x
  assert [not $ useMul s]
  return (LPOS s)

instance Pretty a => Pretty (LPOSsymbol v a) where
    pPrint = pPrint . unLPOS

-- LPO

newtype LPOsymbol v a = LPO{unLPO::RPOSsymbol v a}
    deriving (Eq, Ord, Show, HasArity, Hashable
             ,HasPrecedence v, HasFiltering v
             ,UsableSymbol v, DPSymbol, Functor, Foldable)

instance Decode (LPOsymbol v a) (SymbolRes a) v where decode = liftM removePerm . decode . unLPO

removePerm symbolRes@SymbolRes{status=Lex _} = symbolRes{status = Lex Nothing}
removePerm symbolRes = symbolRes

--lpo :: SymbolFactory LPOsymbol
lpo x = do
  s <- rpos x
  assert [not $ useMul s]
  return (LPO s)

instance Pretty a => Pretty (LPOsymbol v a) where pPrint = pPrint . unLPO

instance (Ord v, Show v) => HasStatus v (LPOsymbol v a) where
    useMul_v     = encodeUseMset . unLPO
    lexPerm_vv _ = Nothing

-- MPO
newtype MPOsymbol v a = MPO{unMPO::RPOSsymbol v a}
    deriving (Eq, Ord, Show, HasArity, Hashable
             ,HasPrecedence v, HasStatus v, HasFiltering v
             ,UsableSymbol v, DPSymbol, Functor, Foldable)

instance Decode (MPOsymbol v a) (SymbolRes a) v where decode = decode . unMPO

instance Pretty a => Pretty (MPOsymbol v a) where
    pPrint = pPrint . unMPO

--mpo :: SymbolFactory MPOsymbol
mpo x = do
  s <- rpos x
  assert [useMul  s]
  return (MPO s)

-- RPO
newtype RPOsymbol v a = RPO{unRPO::RPOSsymbol v a}
    deriving (Eq, Ord, Show, HasArity, Hashable
             ,HasPrecedence v, HasStatus v, HasFiltering v
             ,UsableSymbol v, DPSymbol, Functor, Foldable)

instance Decode (RPOsymbol v a) (SymbolRes a) v where decode = liftM removePerm . decode . unRPO

instance Pretty a => Pretty (RPOsymbol v a) where pPrint = pPrint . unRPO

--rpo :: SymbolFactory RPOsymbol
rpo x = do
  s <- rpos x
  return (RPO s)
