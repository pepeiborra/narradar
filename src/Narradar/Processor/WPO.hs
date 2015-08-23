{-# LANGUAGE CPP #-}
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

module Narradar.Processor.WPO ( WPOProc(..)
                              , WPOProof(..)
                              , WPOAlgebra(..)
                              , UsableRulesMode
                              , omegaFor
                              , runWpoProc
                              ) where

import Data.Typeable
import Data.List ((\\), groupBy, sortBy)
import Data.Monoid (Monoid(..))
import qualified Data.Set as Set
import qualified Data.Term.Family as Family

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Constraints.SAT.MonadSAT( Decode(..),Tree,printTree, Var)
import Narradar.Constraints.SAT.Orderings -- (runR, omegaNone, omegaUsable, omegaNeeded)
import Narradar.Constraints.SAT.Usable (isUsable, decodeUsable, symbolRes)
import Narradar.Processor.RPO (UsableRulesMode, omegaFor)

import Funsat.TermCircuit (runEvalM)
import Funsat.TermCircuit.WPO.Symbols as WPO (Status(..), SymbolRes(..))

import Narradar.Utils

import Debug.Hoed.Observe
import Control.Applicative ((<$>))


data WPOAlgebra = POL | SUM deriving (Eq, Ord, Show)
instance Pretty WPOAlgebra where pPrint = text . show

data WPOProc (info :: * -> *) where
  WPOProc :: WPOAlgebra -> UsableRulesMode -> WPOProc info
type instance InfoConstraint (WPOProc info) = info

instance Observable (WPOProc info) where observer = observeOpaque "WPO Processor"

data WPOProof id where
  WPOProof :: Pretty (RuleN id) =>
              WPOAlgebra
           -> [RuleN id]  -- ^ Strictly decreasing dps
           -> [RuleN id]  -- ^ Usable rules
           -> [WPO.SymbolRes id]
           -> [Tree (TermN id) Var]
           -> WPOProof id

  WPOFail ::  WPOAlgebra -> WPOProof id

     deriving Typeable

instance (Ord id, Pretty id) => Eq (WPOProof id) where a == b = pPrint a == pPrint b
instance (Ord id, Pretty id) => Ord (WPOProof id) where compare a b = pPrint a `compare` pPrint b
instance Observable1 WPOProof where observer1 = observeOpaque "WPOProof"
instance Observable a => Observable (WPOProof a) where observer = observer1 ; observers = observers1

wpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> WPOProof (Family.Id t)
wpoFail _ = WPOFail POL -- TODO

runWpoProc ob solve mkS cTyp p rpo = f $ solve ob $ runRP ob mkS cTyp p rpo where
  f Nothing = dontKnow (wpoFail p) p
  f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = singleP proof p (setP (restrictTRS dps nondec_dps) p) where

   symbols       = runEvalM bienv $ mapM decodeUsable symbols_raw
   proof         = WPOProof POL decreasingDps usableRules (symbolRes <$> symbols) extraConstraints
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO"
                        ([0..length (rules dps) - 1] \\ nondec_dps)
                        (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR $ symbolRes s | s <- symbols, isUsable s]


instance (Ord id, Pretty id) => Pretty (WPOProof id) where
    pPrint (WPOProof a dps rr ss cc) =
     (if null cc then text "WPO reduction pair" <+> parens(a <+> "algebra")
        else text "WPO reduction pair with the extra constraints" $$
             nest 4 (vcat $ map (printTree 0) cc))
     $$ text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "The status used was:" $$
        nest 4 (vcat the_status) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map pPrint rr) $$
        text "Precedence:" <+> printPrec prec theSymbolR ssPrec
     where
       the_status =
         [ i <+> text "->" <+> j
           | s <- ss
           , Lex nn <- [status s]
           , (i, Just j) <- zip [(0::Int)..] nn]
       relevantSymbols = getAllSymbols (dps `mappend` rr)
       ssPrec = [ s | s <- ss, theSymbolR s `Set.member` relevantSymbols]
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
    pPrint (WPOFail a) =
      text "WPO with" <+> a <+> text "algebra : failed to synthetize a suitable ordering"


printPrec f symb    = fsep
                    . punctuate (text " >")
                    . fmap ( fsep
                           . punctuate (text " =")
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)
