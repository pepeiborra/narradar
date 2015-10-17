{-# LANGUAGE CPP #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Narradar.Processor.WPO ( WPOReductionPair(..), WPOReductionPairProof(..)
                              , WPORuleRemoval(..), WPORuleRemovalProof(..)
                              , WPOAlgebra(..), WPOMonotoneAlgebra(..)
                              , UsableRulesMode
                              , omegaFor
                              , runWpoReductionPair, runWpoRuleRemoval
                              ) where
import Control.Monad (mzero)
import Data.Typeable
import Data.List ((\\), groupBy, sortBy)
import Data.Monoid (Monoid(..))
import qualified Data.Set as Set
import qualified Data.Term.Family as Family

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Constraints.SAT.MonadSAT( Decode(..),Tree,printTree, Var, inAF, EvalM, Tree, BIEnv)
import Narradar.Constraints.SAT.Orderings (reductionPair, runRP, ruleRemoval, omegaNone, omegaUsable', omegaNeeded')
import Narradar.Constraints.SAT.Usable (MkSATSymbol, Usable, isUsable, decodeUsable, symbolRes)
import Narradar.Constraints.SAT.WPO (EnvWPO)
import qualified Narradar.Constraints.SAT.WPO as WPO
import Narradar.Processor.RPO (UsableRulesMode(..))

import Funsat.ECircuit(or, eq, not, fromInteger, nat)
import Funsat.TermCircuit (runEvalM)
import Funsat.TermCircuit.WPO (getC)
import Funsat.TermCircuit.WPO.Symbols (Status(..), SymbolRes(..))
import qualified Funsat.TermCircuit.WPO.Symbols as WPO

import Narradar.Utils

import Debug.Hoed.Observe
import Control.Applicative ((<$>))

import Prelude hiding (fromInteger, or, not)

omegaFor All    = omegaNone
omegaFor Needed = omegaNeeded' inAF'
omegaFor Usable = omegaUsable' inAF'

inAF' i id = inAF i id `or` not (nat(getC id !! pred i) `eq` fromInteger 0)

data WPOAlgebra = LPOAF
                | KBOAF
                | SUM
                | MAX
                | MPOL (Maybe Integer) (Maybe Integer)
                | MSUM
                deriving (Eq, Ord, Show)
data WPOMonotoneAlgebra =
                  POLO (Maybe Integer) (Maybe Integer)
                | LPO
                | KBO
                | TKBO
                deriving (Eq, Ord, Show)

instance Pretty WPOAlgebra where pPrint = text . show

data WPORuleRemoval (info :: * -> *) where
  WPORuleRemoval :: WPOMonotoneAlgebra -> WPORuleRemoval info
type instance InfoConstraint (WPORuleRemoval info) = info
instance Observable (WPORuleRemoval info) where observer = observeOpaque "WPO Rule Removal Processor"

data WPOReductionPair (info :: * -> *) where
  WPOReductionPair :: WPOAlgebra -> UsableRulesMode -> WPOReductionPair info
type instance InfoConstraint (WPOReductionPair info) = info
instance Observable (WPOReductionPair info) where observer = observeOpaque "WPO Reduction Pair Processor"

data WPOReductionPairProof id where
  WPOReductionPairProof :: Pretty (RuleN id) =>
              WPOAlgebra
           -> [RuleN id]  -- ^ Strictly decreasing dps
           -> [RuleN id]  -- ^ Usable rules
           -> [WPO.SymbolRes id]
           -> [Tree (TermN id) Var] -- ^ Additional constraints
           -> WPOReductionPairProof id

  WPOReductionPairFail ::  WPOAlgebra -> WPOReductionPairProof id

     deriving Typeable

data WPORuleRemovalProof id where
  WPORuleRemovalProof :: Pretty (RuleN id) =>
              WPOMonotoneAlgebra
           -> [RuleN id]  -- ^ Strictly decreasing rules
           -> [WPO.SymbolRes id]
           -> [Tree (TermN id) Var] -- ^ Additional constraints
           -> WPORuleRemovalProof id

  WPORuleRemovalFail ::  WPOMonotoneAlgebra -> WPORuleRemovalProof id

     deriving Typeable

instance (Ord id, HasArity id, Pretty id) => Eq (WPOReductionPairProof id) where a == b = pPrint a == pPrint b
instance (Ord id, HasArity id, Pretty id) => Ord (WPOReductionPairProof id) where compare a b = pPrint a `compare` pPrint b
instance Observable1 WPOReductionPairProof where observer1 = observeOpaque "WPOReductionPairProof"
instance Observable a => Observable (WPOReductionPairProof a) where observer = observer1 ; observers = observers1

instance (Ord id, HasArity id, Pretty id) => Eq (WPORuleRemovalProof id) where a == b = pPrint a == pPrint b
instance (Ord id, HasArity id, Pretty id) => Ord (WPORuleRemovalProof id) where compare a b = pPrint a `compare` pPrint b
instance Observable1 WPORuleRemovalProof where observer1 = observeOpaque "WPORuleRemovalProof"
instance Observable a => Observable (WPORuleRemovalProof a) where observer = observer1 ; observers = observers1

wpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> WPOAlgebra -> WPOReductionPairProof (Family.Id t)
wpoFail _ alg = WPOReductionPairFail alg -- TODO

wpoRuleRemovalFail :: Problem typ (NarradarTRS t Narradar.Var) -> WPORuleRemovalProof (Family.Id t)
wpoRuleRemovalFail _ = WPORuleRemovalFail LPO

runWpoReductionPair :: (Family.Id id' ~ id, _) =>
                       Observer
                    -> WPOAlgebra
                    -> _
                    -> MkSATSymbol EnvWPO id'
                    -> ((id -> id') -> typ -> typ')
                    -> (Problem typ' (NTRS id') -> _)
                    -> Problem typ (NTRS id)
                    -> Proof info m (Problem typ (NTRS id))
runWpoReductionPair o alg solve mkS cTyp rpo p
  | null(rules $ getP p) = mzero
  | otherwise = f $ solve o $ runRP o mkS cTyp p rpo
 where
  f Nothing = dontKnow (wpoFail p alg) p
  f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = singleP proof p (setP (restrictTRS dps nondec_dps) p) where

   symbols       = runEvalM bienv $ mapM decodeUsable symbols_raw
   proof         = WPOReductionPairProof alg decreasingDps usableRules (symbolRes <$> symbols) extraConstraints
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.WPO"
                        ([0..length (rules dps) - 1] \\ nondec_dps)
                        (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR $ symbolRes s | s <- symbols, isUsable s]

runWpoRuleRemoval obs@(O o oo) solve mkS cTyp p
  | null(rules $ getR p) = mzero
  | otherwise = f $ solve obs $ runRP obs mkS cTyp p ruleRemoval
 where
  f Nothing = dontKnow (wpoRuleRemovalFail p) p
  f (Just ((nondec_rules, extraConstraints), bienv, symbols_raw))
   = singleP proof p (oo "setR" setRO (restrictTRS trs nondec_rules) p) where

   symbols       = runEvalM bienv $ mapM decodeUsable symbols_raw
   proof         = WPORuleRemovalProof LPO decreasingRules (symbolRes <$> symbols) extraConstraints
   trs           = getR p
   decreasingRules = selectSafe "Narradar.Processor.WPO"
                        ([0..length (rules trs) - 1] \\ nondec_rules)
                        (rules trs)


instance (Ord id, Pretty id, HasArity id) => Pretty (WPOReductionPairProof id) where
    pPrint (WPOReductionPairProof a dps rr ss cc) =
     (if null cc then text "WPO reduction pair" -- <+> parens(a <+> text "algebra")
        else text "WPO reduction pair with the extra constraints" $$
             nest 4 (vcat $ map (printTree 0) cc))
     $$ text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "The status used was:" $$
        nest 4 (vcat the_status) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map pPrint rr) $$
        text "Precedence:" <+> printPrec prec theSymbolR ssPrec $$
--        text "W_0: " $$
        text "Algebra:" $$
        nest 4 (vcat algebras)
     where
       the_status =
         [ s <> colon <+>
            punctuate comma
             [ i <+> text "->" <+> j
             | Lex nn <- [status s]
             , (i, Just j) <- zip [(0::Int)..] nn ]
           | s <- ss]

       relevantSymbols = getAllSymbols (dps `mappend` rr)
       ssPrec = [ s | s <- ss, theSymbolR s `Set.member` relevantSymbols]
       algebras =
         [ theSymbolR s <> par(pun "," args) <+> text "=" <+>
           case algebra s of
             WPO.SUM -> hsep $ pun " +" (pPrint (weight s) : args)
             WPO.POL -> hsep $ pun " +" (pPrint (weight s) : [ c <> text "*" <> arg | (c,arg) <- zip (cs s) args ])
             WPO.MAX
               | ar == 0 -> pPrint(weight s)
               | ar == 1 -> head(cp s) <+> text "+" <+> head args
               | otherwise ->
                        text "max" <> par(pun "," [ c <+> text "+" <+> arg | (c,arg) <- zip (cp s) args ])

           | s <- ss
           , let ar   = getIdArity $ theSymbolR s
           , let args = take ar $ map pPrint "xyzwutabcde"
           ]

       par [] = mempty
       par xx = parens(hsep xx)
       pun txt = punctuate (text txt)
{-
    pPrint (RPOProof dps _ ss) =
        text "Monotonic RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "Precedence:" <+> printPrec RPO.precedence RPO.theSymbolR ss $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPO.SymbolRes{..} <- ss])
-}
    pPrint (WPOReductionPairFail a) =
      text "WPO with" <+> a <+> text "algebra : failed to synthetize a suitable ordering"


printPrec f symb    = fsep
                    . punctuate (text " >")
                    . fmap ( fsep
                           . punctuate (text " =")
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)


instance (Ord id, Pretty id, HasArity id) => Pretty (WPORuleRemovalProof id) where
    pPrint (WPORuleRemovalProof a rr ss cc) =
     (if null cc then text "WPO rule removal" -- <+> parens(a <+> text "algebra")
        else text "WPO rule removal with the extra constraints" $$
             nest 4 (vcat $ map (printTree 0) cc))
     $$ text "The following rules are strictly decreasing:" $$
        nest 4 (vcat (map pPrint rr)) $$
        text "Precedence:" <+> printPrec prec theSymbolR ss $$
--        text "W_0: " $$
        text "Algebra:" $$
        nest 4 (vcat algebras)
     where
       the_status =
         [ s <> colon <+>
            punctuate comma
             [ i <+> text "->" <+> j
             | Lex nn <- [status s]
             , (i, Just j) <- zip [(0::Int)..] nn ]
           | s <- ss]

       algebras =
         [ theSymbolR s <> par(pun "," args) <+> text "=" <+>
           case algebra s of
             WPO.SUM -> hsep $ pun " +" (pPrint (weight s) : args)
             WPO.POL -> hsep $ pun " +" (pPrint (weight s) : [ c <> text "*" <> arg | (c,arg) <- zip (cs s) args ])
             WPO.MAX
               | ar == 0 -> pPrint(weight s)
               | ar == 1 -> head(cp s) <+> text "+" <+> head args
               | otherwise ->
                        text "max" <> par(pun "," [ c <+> text "+" <+> arg | (c,arg) <- zip (cp s) args ])

           | s <- ss
           , let ar   = getIdArity $ theSymbolR s
           , let args = take ar $ map pPrint "xyzwutabcde"
           ]

       par [] = mempty
       par xx = parens(hsep xx)
       pun txt = punctuate (text txt)
{-
    pPrint (RPOProof dps _ ss) =
        text "Monotonic RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "Precedence:" <+> printPrec RPO.precedence RPO.theSymbolR ss $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPO.SymbolRes{..} <- ss])
-}
    pPrint (WPORuleRemovalFail a) =
      text "WPO rule removal: failed to synthetize a suitable ordering"

