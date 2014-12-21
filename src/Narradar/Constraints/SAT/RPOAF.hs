{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE EmptyDataDecls #-}

module Narradar.Constraints.SAT.RPOAF (
--   UsableSymbolRes(..), prec, filtering, status, theSymbolR
  RPOSsymbol(..), RPOsymbol(..), LPOsymbol(..), LPOSsymbol(..), MPOsymbol(..)
  ,RPOProblemN, RPOId, EnvRPO(..)
  ,rpo, rpos, lpo, lpos, mpo
  ,check
  ) where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Control.Monad.Cont
import Control.Monad.List
import Data.Foldable (toList)
import Data.List ((\\))
import Data.Maybe
import Data.Hashable
import qualified Data.Set as Set
import Funsat.ECircuit(Natural(..))
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.RPO ()
import qualified Funsat.TermCircuit.RPO.Symbols as Funsat
import Funsat.TermCircuit.RPO.Symbols
  (LPOSsymbol(..), LPOsymbol(..), MPOsymbol(..), RPOSsymbol(..), RPOsymbol(..) )

import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.SAT.MonadSAT
import Narradar.Constraints.SAT.Usable
import Narradar.Framework
import Narradar.Types (DPSymbol(..), HasArity(..), GenSymbol(..))
import Narradar.Types.Term
import Narradar.Types.Problem
import Narradar.Utils hiding (none)

import qualified Data.Term.Family as Family
import qualified Narradar.Types.ArgumentFiltering as AF
import qualified Prelude as P
import Prelude hiding (lex, not, and, or, any, all, quot, (>))

import Debug.Hoed.Observe

-- TODO apply these constraint synonyms consistently across this file
type RPOId id = (FrameworkId id, UsableSymbol id, IsSimple id, HasLexMul id, HasPrecedence id, HasStatus id, HasFiltering id, DPSymbol id)
type RPOProblemN typ id = (FrameworkProblemN typ id, RPOId id, NeededRules (NProblem typ id))

-- -------------------
-- MkSATSymbol
-- -------------------

data EnvRPO (repr :: * -> *) v

rpos :: MkSATSymbol EnvRPO (Usable (RPOSsymbol Var id))
rpo  :: MkSATSymbol EnvRPO (Usable (RPOsymbol  Var id))
lpos :: MkSATSymbol EnvRPO (Usable (LPOSsymbol Var id))
lpo  :: MkSATSymbol EnvRPO (Usable (LPOsymbol  Var id))
mpo  :: MkSATSymbol EnvRPO (Usable (MPOsymbol  Var id))
rpos  = MkSATSymbol (makeUsableSymbol Funsat.rpos)
rpo   = MkSATSymbol (makeUsableSymbol Funsat.rpo)
lpos  = MkSATSymbol (makeUsableSymbol Funsat.lpos)
lpo   = MkSATSymbol (makeUsableSymbol Funsat.lpo)
mpo   = MkSATSymbol (makeUsableSymbol Funsat.mpo)

type UsableRPOSsymbol v id = Usable (RPOSsymbol v id)

-- ----------------------------------
-- Narradar instances for RPO symbols
-- ----------------------------------

type instance SymbolRes (RPOSsymbol v a) = Funsat.SymbolRes a
type instance SymbolRes (LPOSsymbol v a) = Funsat.SymbolRes a
type instance SymbolRes (RPOsymbol  v a) = Funsat.SymbolRes a
type instance SymbolRes (LPOsymbol  v a) = Funsat.SymbolRes a
type instance SymbolRes (MPOsymbol  v a) = Funsat.SymbolRes a

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

instance Decode (RPOSsymbol v a) (Funsat.SymbolRes a) where decode = decodeSymbol
instance Decode (LPOSsymbol v a) (Funsat.SymbolRes a) where decode = decode . unLPOS
instance Decode (LPOsymbol v a)  (Funsat.SymbolRes a) where decode = liftM removePerm . decode . unLPO
instance Decode (MPOsymbol v a ) (Funsat.SymbolRes a) where decode = decode . unMPO
instance Decode (RPOsymbol v a)  (Funsat.SymbolRes a) where decode = liftM removePerm . decode . unRPO


instance Observable1 (RPOSsymbol v) where observer1 = observeOpaque "rpos-symbol"
instance Observable1 (RPOsymbol v)  where observer1 = observeOpaque "rpo-symbol"
instance Observable1 (LPOSsymbol v) where observer1 = observeOpaque "lpos-symbol"
instance Observable1 (LPOsymbol v)  where observer1 = observeOpaque "lpo-symbol"
instance Observable1 (MPOsymbol v)  where observer1 = observeOpaque "mpo-symbol"
instance Observable a => Observable (RPOSsymbol v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (RPOsymbol  v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (LPOSsymbol v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (LPOsymbol  v a) where observer = observer1 ; observers = observers1
instance Observable a => Observable (MPOsymbol  v a) where observer = observer1 ; observers = observers1

-- --------------------------------------
-- Support for Goal-problems identifiers
-- --------------------------------------

instance (Show a, GenSymbol a) => GenSymbol (RPOSsymbol Var a) where
    genSymbol = Symbol{ theSymbol    = genSymbol
                      , encodePrec   = Natural(V Nothing 10)
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

-- ----------------------
-- Symbols set extensions
-- ----------------------

instance (Eq a, TermCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr) =>
    TermExtCircuit repr (Usable (RPOSsymbol v a)) where
     exEq s t ss tt =
       and [useMul s, useMul t, muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpeq s t ss tt]

     exGt s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt s t ss tt]

     exGe s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt \/ muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt s t ss tt \/ lexpeq s t ss tt]
{-
     exGe s t ss tt =
       and [useMul s, useMul t, mulge s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpge_exist s t ss tt]
-}

instance (TermCircuit repr, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Ord a, Pretty a) =>
  TermExtCircuit repr (Usable(LPOSsymbol v a)) where
  exEq s t = lexpeq s t
  exGt s t = lexpgt s t
--  exGe = lexpge_exist

instance (TermCircuit repr, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Pretty a, Ord a) =>
  TermExtCircuit repr (Usable(LPOsymbol v a)) where
  exEq s t = lexeq s t
  exGt s t = lexgt s t

instance (TermCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Pretty a, Ord a) =>
  TermExtCircuit repr (Usable(MPOsymbol v a)) where
  exEq s t = muleq s t
  exGt s t = mulgt s t

instance (TermCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Pretty a, Ord a) =>
  TermExtCircuit repr (Usable(RPOsymbol v a)) where
  exEq s t ss tt =
      and [ useMul s, useMul t, muleq s t ss tt]
      \/
      and [not$ useMul s, not$ useMul t, lexeq s t ss tt]

  exGt s t ss tt =
      and [useMul s, useMul t, mulgt s t ss tt]
      \/
      and [not$ useMul s, not$ useMul t, lexgt s t ss tt]

-- --------
-- Testing
-- --------

check ::       ( rule ~ RuleF term
               , term ~ Term (TermF id) var
               , rule ~ Family.Rule trs
               , id   ~ Family.Id trs
               , var  ~ Family.Var trs
               , var  ~ Family.Var id
               , var  ~ Family.Var var
               , TermF id ~ Family.TermF trs
--               , Narradar.Var ~ var
               , Enum var, Ord var, GetVars var, Hashable var, Show var, Rename var
               , Decode var Bool
               , FrameworkProblem typ trs
               , HasSignature (Problem typ trs)
               , RPOId id, IsSimple id
               ) =>
               Problem typ trs -> [Int] -> EvalM var (VerifyRPOAF rule)
check p nonDecPairsIx = do
  let the_pairs = getP p
      the_rules = getR p
      npairs    = length $ rules the_pairs
  theAf <- AF.fromList' `liftM` mapM getFiltering (toList $ getAllSymbols signature)
  let theFilteredPairs = rules $ AF.apply theAf the_pairs

  let theWeakPairs = CE.assert (P.all (P.< npairs) nonDecPairsIx) $
                     selectSafe "verifyRPOAF 1" nonDecPairsIx (rules the_pairs)
      theDecPairs  = selectSafe "verifyRPOAF 2" ([0..npairs - 1] \\ nonDecPairsIx) (rules the_pairs)

  theUsableRules <- liftM Set.fromList $ runListT $ do
                       l:->r <- msum $ map return $ rules the_rules
                       let Just id = rootSymbol l
                       guard =<< lift (evalDecode $ input $ usable id)
                       return (l:->r)

  let expectedUsableRules =
        Set.fromList
         [ rule
         | let urAf = Set.fromList $
                      rules$ getR (iUsableRules' p [] (rhs <$> theFilteredPairs))
         , rule <- rules the_rules
         , AF.apply theAf rule `Set.member` urAf]

  falseDecreasingPairs <- runListT $ do
     s:->t <- li theDecPairs
     guard =<< lift (evalDecode $ not(s > t))
     return (s:->t)

  falseWeaklyDecreasingPairs <- runListT $ do
     s:->t <- li theWeakPairs
     guard =<< lift (evalDecode $ not( s >~  t))
     return (s:->t)

  falseWeaklyDecreasingRules <- runListT $ do
     s:->t <- li (toList theUsableRules)
     guard =<< lift (evalDecode $ not( s >~  t))
     return (s:->t)

  let missingUsableRules = [] -- toList (Set.difference expected_usableRules the_usableRules)
      excessUsableRules  = [] -- toList (Set.difference the_usableRules expected_usableRules)

  return VerifyRPOAF{thePairs = rules the_pairs, ..}

 where
  signature = getSignature p
  getFiltering s = do
    isListAF   <- evalDecode $ listAF s
    filterings <- mapM decode (filtering_vv s)
    let positions = [ i | (i,True) <- zip [1..(getArity signature s)] filterings]
    return $ if isListAF
              then (s, Right positions)
              else case positions of
                     [p] -> (s, Left p)
                     _   -> error ("Invalid collapsing filtering " ++ show positions ++
                                   " for symbol " ++ show (pPrint s))
