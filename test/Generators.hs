{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Generators where

import Control.Applicative ((<$>), (<$), pure)
import Control.Monad (liftM, liftM2, liftM3, replicateM)
import Control.Monad.State (MonadState(..), modify, StateT, runState, evalStateT)
import Control.Monad.Trans(MonadTrans(..))
import Data.Hashable (Hashable(..))
import Data.Map (Map)
import Data.Foldable(toList)
import Data.Traversable(traverse)
import Text.PrettyPrint.HughesPJClass
import Test.QuickCheck

import qualified Data.Map as Map

import Funsat.Circuit      as C
import Funsat.ECircuit     as EC
import Funsat.RPOCircuit   as RPOC

import Narradar.Types as Narradar hiding (G,V)
import Narradar.Constraints.SAT.MonadSAT as SAT
import Narradar.Constraints.SAT.Solve
import Narradar.Constraints.SAT.RPOAF hiding (mkSATSymbol)
import Narradar.Constraints.SAT.RPOAF.Symbols

import Types

-- -----------------------
-- Generating Vars and Ids
-- -----------------------

instance Arbitrary NVar where
  arbitrary = do {con <- elements [VB,VN]; (con . abs) `liftM` arbitrary}

instance Decode NVar Bool NVar where decode v@VB{} = evalB (input v)

instance Arbitrary RandId where
  arbitrary = elements [ F,G,F2,G2,S,Z]
  shrink F2 = [F]
  shrink G2 = [G]
  shrink _  = []


-- ----------------
-- Generating Terms
-- ----------------

type LPOId = LPOsymbol NVar RandId
type LDPId = LPOsymbol SAT.Var DPRandId
type MDPId = MPOsymbol SAT.Var DPRandId
type RDPId = RPOsymbol SAT.Var DPRandId
type LSDPId = LPOSsymbol SAT.Var DPRandId
--type RDPId = SymbolRes DPRandId

instance IsDefined a => IsDefined (RPOSsymbol v a) where isDefined = isDefined . theSymbol
deriving instance IsDefined a => IsDefined (LPOsymbol v a)
deriving instance IsDefined a => IsDefined (MPOsymbol v a)
deriving instance IsDefined a => IsDefined (RPOsymbol v a)
deriving instance IsDefined a => IsDefined (LPOSsymbol v a)

mkSATSymbol mk F  = mk (IdFunction F, 1, True)
mkSATSymbol mk G  = mk (IdFunction G, 1, True)
mkSATSymbol mk F2 = mk (IdFunction F2, 2, True)
mkSATSymbol mk G2 = mk (IdFunction G2, 2, True)
mkSATSymbol mk S  = mk (IdFunction S, 1, False)
mkSATSymbol mk Z  = mk (IdFunction Z, 0,False)

-- * Construction of symbols with fresh variables from a monadic supply

mkSATSymbol' :: (MonadState (Map RandId id') (t m), Monad m, MonadTrans t) =>
                ((DPRandId, Int, Bool) -> m id') -> RandId -> t m id'
mkSATSymbol' mk s = do
  dict <- get
  case Map.lookup s dict of
             Just sat -> return sat
             _        -> do
               s' <- lift $ mkSATSymbol mk s
               modify (Map.insert s s')
               return s'

-- * Hardcoded construction of symbols
mkSymbol F = createSymbol 0 0 F 1
mkSymbol G = createSymbol 5 2 G 1
mkSymbol S = createSymbol 10 4 S 1
mkSymbol Z = createSymbol 15 6 Z 0
mkSymbol F2 = createSymbol 20 8 F2 2
mkSymbol G2 = createSymbol 30 10 G2 2

createSymbol ::  Show id => Int -> Int -> id -> Int -> LPOsymbol NVar id
createSymbol b0 n0 id 2
  = LPO $ Symbol
              { theSymbol    = id
              , encodePrec   = encodeNatural prec
              , encodeUsable = vb 1
              , encodeAFlist = vb 2
              , encodeAFpos  = [vb 3, vb 4]
              , encodePerm   = [[vb 5, vb 6], [vb 7, vb 8]]
              , encodeUseMset= vb 9
              , decodeSymbol = mkSymbolDecoder id prec (vb 1) (vb 2) [vb 3, vb 4] [[vb 5, vb 6], [vb 7, vb 8]] (vb 9)
              }

 where
  vb i = VB (b0 + i)
  vn i = VN (n0 + i)
  prec = Natural (vn 1)

createSymbol b0 n0 id 1
  = LPO $ Symbol
              { theSymbol    = id
              , encodePrec   = encodeNatural prec
              , encodeUsable = vb 1
              , encodeAFlist = vb 2
              , encodeAFpos  = [vb 3]
              , encodePerm   = [[vb 4]]
              , encodeUseMset= vb 5
              , decodeSymbol = mkSymbolDecoder id prec (vb 1) (vb 2) [vb 3] [[vb 4]] (vb 5)
              }

 where
  vb i = VB (b0 + i)
  vn i = VN (n0 + i)
  prec = Natural (vn 1)

createSymbol b0 n0 id 0
  = LPO $ Symbol
              { theSymbol = id
              , encodePrec = encodeNatural prec
              , encodeUsable = vb 1
              , encodeAFlist = vb 2
              , encodeAFpos  = []
              , encodePerm   = []
              , encodeUseMset = vb 3
              , decodeSymbol = mkSymbolDecoder id prec (vb 1) (vb 2) [] [] (vb 3)}
 where
  vb i = VB (b0 + i)
  vn i = VN (n0 + i)
  prec = Natural (vn 1)


-- manual testing using the hardcoded construction of symbols
f x = term (mkSymbol F) [x]
g x = term (mkSymbol G) [x]
s x = term (mkSymbol S) [x]
z   = term (mkSymbol Z) []
f2 x y = term (mkSymbol F2) [x,y]
g2 x y = term (mkSymbol G2) [x,y]
v0 = var 0
v1 = var 1

sizedTerm, sizedDefTerm :: (HasArity id, IsDefined id, Arbitrary id) => Int -> Gen (TermN id)
sizedTerm size = oneof [return $ Narradar.var 0
                       ,return $ Narradar.var 1
                       ,do
  id <- arbitrary
  let ar = getIdArity id
  tt <- replicateM ar (sizedTerm (size `div` (1 + ar)))
  return (term id tt)]

sizedDefTerm size = do
  id <- arbitrary `suchThat` isDefined
  let ar = getIdArity id
  tt <- replicateM ar (sizedTerm (size `div` (1 + ar)))
  return (term id tt)

instance (HasArity id, IsDefined id, Arbitrary id) => Arbitrary (TermN id)
  where
   arbitrary = sized sizedTerm
   shrink (Impure (Term id tt)) = [Impure (Term id' tt') | id' <- shrink id ++ [id]
                                                         , tt' <- take (getIdArity id) $ mapM shrink tt]
   shrink t = []

instance (HasArity id, IsDefined id, Arbitrary id) => Arbitrary (RuleN id)
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      return ( lhs :-> rhs )
   shrink (l :-> r) = init [ l' :-> r' | l' <- shrink l ++ [l], r' <- shrink r ++ [r]]

instance Arbitrary (SAT' RandId LPOsymbol SAT.Var (RuleN LDPId))
  where
   arbitrary = do
      lhs :: TermN RandId <- sized sizedDefTerm
      rhs :: TermN RandId <- sized sizedTerm
      let rule  = lhs :-> rhs :: RuleN RandId

      return $ traverse (mapTermSymbolsM (mkSATSymbol' lpo)) rule

instance Arbitrary (SAT' RandId MPOsymbol SAT.Var (RuleN (MPOsymbol SAT.Var DPRandId)))
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      let rule  = lhs :-> rhs
      return $ traverse (mapTermSymbolsM (mkSATSymbol' mpo)) rule

instance Arbitrary (SAT' RandId LPOSsymbol SAT.Var (RuleN (LPOSsymbol SAT.Var DPRandId)))
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      let rule  = lhs :-> rhs
      return $ traverse (mapTermSymbolsM (mkSATSymbol' lpos)) rule


-- -------------------------------
-- Generation of circuits as trees
-- -------------------------------

sizedCircuit :: (Co c SAT.Var, Circuit c) => Int -> Gen (c SAT.Var)
sizedCircuit 0 = return . input . V $ 1
sizedCircuit n =
    oneof [ return true
          , return false
          , (return . input . V) n
          , liftM2 EC.and subcircuit2 subcircuit2
          , liftM2 EC.or  subcircuit2 subcircuit2
          , liftM EC.not subcircuit1
          ]
  where subcircuit2 = sizedCircuit (n `div` 2)
        subcircuit1 = sizedCircuit (n - 1)


-- | Generator for a circuit containing at most `n' nodes, involving only the
-- literals 1 .. n.
sizedECircuit :: (Co c SAT.Var, ECircuit c) => Int -> Gen (c SAT.Var)
sizedECircuit 0 = return . input . V $ 1
sizedECircuit n =
    oneof [ return true
          , return false
          , (return . input . V) n
          , liftM2 EC.and subcircuit2 subcircuit2
          , liftM2 EC.or  subcircuit2 subcircuit2
          , liftM EC.not subcircuit1
          , liftM3 ite subcircuit3 subcircuit3 subcircuit3
          , liftM2 onlyif subcircuit2 subcircuit2
          , liftM2 EC.iff subcircuit2 subcircuit2
          , liftM2 xor subcircuit2 subcircuit2
          ]
  where subcircuit3 = sizedECircuit (n `div` 3)
        subcircuit2 = sizedECircuit (n `div` 2)
        subcircuit1 = sizedECircuit (n - 1)

-- | Generator for a circuit containing at most `n' nodes, involving only the
-- literals 1 .. n.
sizedOneCircuit :: (Co c SAT.Var, ECircuit c, OneCircuit c) => Int -> Gen (c SAT.Var)
sizedOneCircuit 0 = return . input . V $ 1
sizedOneCircuit n =
    oneof [ return true
          , return false
          , (return . input . V) n
          , liftM2 EC.and subcircuit2 subcircuit2
          , liftM2 EC.or  subcircuit2 subcircuit2
          , liftM EC.not subcircuit1
          , return $ one (map (input.V) [0..n])
          ]
  where subcircuit2 = sizedOneCircuit (n `div` 2)
        subcircuit1 = sizedOneCircuit (n - 1)


sizedNatCircuit :: (Co c NVar, Co c SAT.Var, Functor c, ECircuit c, OneCircuit c, NatCircuit c) => Int -> Gen (c NVar)
sizedNatCircuit 0 = return . vb $ 1
sizedNatCircuit n =
    oneof [ return true
          , return false
          , (return . vb) n
          , liftM2 EC.and subcircuit2 subcircuit2'
          , liftM2 EC.or  subcircuit2 subcircuit2'
          , liftM EC.not subcircuit1
          , return $ eq (mkNat n) (mkNat (n-1))
          , return $ lt (mkNat n) (mkNat (n-1))
          ]
  where subcircuit2  = sizedNatCircuit (n `div` 2)
        subcircuit1  = sizedNatCircuit (n - 1)
        subcircuit2' = (fmap.fmap) convert $ sizedCircuit (n `div` 2)
        convert (V i)= VB i
        mkNat = EC.nat . VN

sizedOneNatECircuit :: (Co c NVar, Co c SAT.Var, Functor c, ECircuit c, OneCircuit c, NatCircuit c) => Int -> Gen (c NVar)
sizedOneNatECircuit 0 = return . input . VB $ 1
sizedOneNatECircuit n =
    oneof [ return true
          , return false
          , (return . input . VB) n
          , liftM2 EC.and subcircuit2 subcircuit2'
          , liftM2 EC.or  subcircuit2 subcircuit2'
          , liftM EC.not subcircuit1
          , liftM3 ite subcircuit3' subcircuit3 subcircuit3'
          , liftM2 onlyif subcircuit2 subcircuit2'
          , liftM2 EC.iff subcircuit2 subcircuit2'
          , liftM2 xor subcircuit2 subcircuit2'
          , return $ eq (mkNat n) (mkNat (n-1))
          , return $ lt (mkNat n) (mkNat (n-1))
          , return $ one (map (input.VB) [0..n])
          ]
  where subcircuit3  = sizedOneNatECircuit (n `div` 3)
        subcircuit2  = sizedOneNatECircuit (n `div` 2)
        subcircuit1  = sizedOneNatECircuit (n - 1)
        subcircuit2' = (fmap.fmap) vb $ sizedOneCircuit (n `div` 2)
        subcircuit3' = (fmap.fmap) vb $ sizedOneCircuit (n `div` 3)
        mkNat        = EC.nat .  VN
        vb (V i)     = VB i

sizedxPOCircuit :: forall c (lpoid :: * -> * -> *) id.
                   (HasPrecedence SAT.Var id, HasStatus SAT.Var id, HasFiltering SAT.Var id
                   ,id ~ lpoid SAT.Var DPRandId
                   ,Ord id, Hashable id
                   ,ECircuit c, OneCircuit c, NatCircuit c, RPOCircuit c (TermN id)
                   ,Co c SAT.Var, CoRPO c (TermN id) SAT.Var
                   ,Arbitrary (SAT' RandId lpoid SAT.Var (RuleN id))
                   ) => Proxy id -> Int -> Gen (c SAT.Var, Int)
sizedxPOCircuit _ size = do
  c <- go size
  let (circuit, St pool constraints _) = runSAT' c
  return (circuit /\ removeExist (RPOC.runShared constraints), fromEnum (head pool))
 where
  go :: Int -> Gen (SAT' RandId lpoid SAT.Var (c SAT.Var))
  go 0 = return . return . input . V $ 1
  go n =
    oneof [ return (return true)
          , return (return false)
          , (return . return . input . V) n
          , (liftM2.liftM2) EC.and subcircuit2 subcircuit2
          , (liftM2.liftM2) EC.or  subcircuit2 subcircuit2
          , (liftM.liftM)   EC.not subcircuit1
          , termConstraint
          ]
     where
        subcircuit2    = go (n `div` 2)
        subcircuit1    = go (n - 1)
        termConstraint = do
          rule <- arbitrary
          cmp  <- elements [termGt, termEq]
          return $ liftM (\(l:->r) -> cmp l r) rule

type SizedGen a = Int -> Gen a
type ShrinkableSizedGen a = (a->[a], SizedGen a)

sizedLPOCircuit :: forall c. (Co c SAT.Var, CoRPO c (TermN (LDPId)) SAT.Var, ECircuit c, OneCircuit c, NatCircuit c, RPOCircuit c (TermN LDPId)) => SizedGen (c SAT.Var, Int)
sizedLPOCircuit = sizedxPOCircuit undefined -- :: LPOsymbol Var DPId)

sizedMPOCircuit :: forall c. (Co c SAT.Var, CoRPO c (TermN (MPOsymbol SAT.Var DPRandId)) SAT.Var, ECircuit c, OneCircuit c, NatCircuit c, RPOCircuit c (TermN MDPId)) => SizedGen (c SAT.Var, Int)
sizedMPOCircuit = sizedxPOCircuit undefined

sizedLPOsCircuit :: forall c.
                    ( Co c SAT.Var
                    , CoRPO c (TermN (LPOSsymbol SAT.Var DPRandId)) SAT.Var
                    , ECircuit c, OneCircuit c, NatCircuit c
                    , RPOCircuit c (TermN LSDPId)
                    ) => SizedGen (c SAT.Var, Int)
sizedLPOsCircuit = sizedxPOCircuit undefined -- :: LPOSsymbol Var DPId)

instance OneCircuit EC.Tree

-- Arbitrary instances for circuits

instance Arbitrary (EC.Tree SAT.Var) where
    arbitrary = sized sizedECircuit
    shrink    = shrinkETree
instance Arbitrary (RPOC.Tree id SAT.Var) where
    arbitrary = sized sizedCircuit
    shrink    = shrinkTree
instance Arbitrary (RPOC.Tree id NVar) where
    arbitrary = sized sizedOneNatECircuit
    shrink    = shrinkTree


shrinkTree (RPOC.TFix(RPOC.TAnd a b)) =
    [a, b] ++ tail[RPOC.tAnd a' b'
                   | a' <- a:shrinkTree a
                   , b' <- b:shrinkTree b]

shrinkTree (RPOC.TFix(RPOC.TOr a b))  =
    [a,b] ++ tail[RPOC.tOr a' b'
                  | a' <- a:shrinkTree a
                  , b' <- b:shrinkTree b]
shrinkTree (RPOC.TFix(RPOC.TIff a b)) =
    [a,b] ++ tail [RPOC.tIff a' b'
                   | a' <- a:shrinkTree a
                   , b' <- b:shrinkTree b]

shrinkTree (RPOC.TFix(RPOC.TOnlyIf a b)) =
    [a,b] ++ tail [RPOC.tOnlyIf a' b'
                   | a' <- a:shrinkTree a
                   , b' <- b:shrinkTree b]
shrinkTree (RPOC.TFix(RPOC.TXor a b)) =
    [a,b] ++ tail[RPOC.tXor a' b'
                  | a' <- a:shrinkTree a
                  , b' <- b:shrinkTree b]
shrinkTree (RPOC.TFix(RPOC.TNot a))   = [a] ++ tail[RPOC.tNot a' | a' <- shrinkTree a]
shrinkTree (RPOC.TFix(RPOC.TIte a b c)) =
    [a,b,c] ++ tail[RPOC.tIte a b c
                   | a' <- a:shrinkTree a
                   , b' <- b:shrinkTree b
                   , c' <- c:shrinkTree c]
shrinkTree (RPOC.TFix(RPOC.TEq uu vv)) =
    [RPOC.tEq uu' vv'
    | uu' <- shrinkTree uu
    , vv' <- shrinkTree vv]
shrinkTree (RPOC.TFix(RPOC.TLt uu vv)) =
    [RPOC.tLt uu' vv'
     | uu' <- shrinkTree uu
     , vv' <- shrinkTree vv]
shrinkTree (RPOC.TFix(RPOC.TOne (_:vv))) = [RPOC.tOne vv]
shrinkTree t = []




shrinkETree (EC.TIff a b) = [a,b] ++ tail [EC.TIff a' b' | a' <- a:shrinkETree a
                                                         , b' <- b:shrinkETree b]
shrinkETree (EC.TOnlyIf a b) = [a,b] ++ tail [EC.TOnlyIf a' b'
                                              | a' <- a:shrinkETree a
                                              , b' <- b:shrinkETree b]
shrinkETree (EC.TXor a b) = [a,b] ++ tail[EC.TXor a' b' | a' <- a:shrinkETree a
                                                 , b' <- b:shrinkETree b]
shrinkETree (EC.TNot a)   = [a] ++ tail[EC.TNot a' | a' <- shrinkETree a]
shrinkETree (EC.TIte a b c) = [a,b,c] ++ tail[EC.TIte a b c
                                              | a' <- a:shrinkETree a
                                              , b' <- b:shrinkETree b
                                              , c' <- c:shrinkETree c]
shrinkETree (EC.TEq uu vv) = [EC.TEq uu' vv' | uu' <- shrinkETree uu
                                      , vv' <- shrinkETree vv]
shrinkETree (EC.TLt uu vv) = [EC.TLt uu' vv' | uu' <- shrinkETree uu
                                      , vv' <- shrinkETree vv]
shrinkETree t = []
