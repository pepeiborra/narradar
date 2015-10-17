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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction, AllowAmbiguousTypes #-}
{-# LANGUAGE PartialTypeSignatures, NamedWildCards #-}

module Narradar.Processor.RPO where

import Control.Applicative
import Data.Proxy
import Data.Typeable (Typeable)
import Data.Type.Equality
import Data.List ((\\), groupBy, sortBy)
import Data.Monoid (Monoid(..))
import qualified Data.Set as Set
import qualified Data.Term.Family as Family

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Constraints.RPO (Status(..))
import Narradar.Constraints.SAT.MonadSAT( Decode(..),Tree,printTree, Var)
import Narradar.Constraints.SAT.Orderings
import Narradar.Constraints.SAT.Usable (Usable, UsableRes(..), decodeUsable)
import Narradar.Utils
--import Narradar.Constraints.SAT.RPOAF ( UsableSymbolRes, theSymbolR, isUsable, filtering, status)

import Funsat.TermCircuit (EvalM, runEvalM)
import Funsat.TermCircuit.RPO.Symbols as RPO (SymbolRes(..),prec)

import Debug.Hoed.Observe

type AllowCol = Bool

data RPOProc (info :: * -> *) where
  RPOProc :: Extension -> UsableRulesMode -> AllowCol -> RPOProc info
type instance InfoConstraint (RPOProc info) = info
instance Observable (RPOProc info) where observer = observeOpaque "RPO processor"

data RPORuleRemoval (info :: * -> *) where
  RPORuleRemoval :: Extension -> RPORuleRemoval info
type instance InfoConstraint (RPORuleRemoval info) = info
instance Observable (RPORuleRemoval info) where observer = observeOpaque "RPO rule removal"

data RPORuleRemovalProof id where
  RPORuleRemovalProof :: Pretty (RuleN id) =>
              Extension
           -> [RuleN id]  -- ^ Strictly decreasing rules
           -> [SymbolRes id]
           -> [Tree (TermN id) Var] -- ^ Additional constraints
           -> RPORuleRemovalProof id

  RPORuleRemovalFail ::  Extension -> RPORuleRemovalProof id

     deriving Typeable

instance (Ord id, HasArity id, Pretty id) => Eq (RPORuleRemovalProof id) where a == b = pPrint a == pPrint b
instance (Ord id, HasArity id, Pretty id) => Ord (RPORuleRemovalProof id) where compare a b = compare (pPrint a) (pPrint b)
instance Observable1 RPORuleRemovalProof where observer1 = observeOpaque "RPORuleRemovalProof"
instance Observable id => Observable (RPORuleRemovalProof id) where observer = observer1 ; observers = observers1

-- TODO
rpoRuleRemovalFail :: Problem typ (NarradarTRS t Narradar.Var) -> RPORuleRemovalProof (Family.Id t)
rpoRuleRemovalFail _ = RPORuleRemovalFail LPOSAF

runRpoRuleRemoval obs@(O o oo) solve mkS cTyp p =
  case oo "solve" solve (runR obs mkS cTyp p ruleRemoval) of
   Nothing -> dontKnow (rpoRuleRemovalFail p) p
   Just ((nondec_rules, extraConstraints), bienv, symbols_raw) ->
     let symbols       = runEvalM bienv $ mapM decodeUsable symbols_raw
         proof         = RPORuleRemovalProof LPOSAF decreasingRules (symbolRes <$> symbols) extraConstraints
         trs           = getR p
         decreasingRules = selectSafe "Narradar.Processor.RPO"
                        ([0..length (rules trs) - 1] \\ nondec_rules)
                        (rules trs)
     in  singleP proof p (oo "setR" setRO (restrictTRS trs nondec_rules) p)


{-
  Some combinations are not safe. The ones I am aware of right now:
   - Existentials are only safe in the SMTFFI backed. Therefore:
   - SMTSerial cannot do MPO because the MPO encoding uses existentials
   - Some of the LPOS encodings have existentials disabled. Ideally we
   - would enable them only in the FFI encoding

 -}
data Extension       = RPOSAF | RPOAF | LPOSAF | LPOAF | MPOAF deriving (Eq, Ord, Show)
data UsableRulesMode = All | Usable | Needed deriving (Eq, Ord, Show)

instance Pretty Extension where pPrint = text . show

omegaFor All    = omegaNone
omegaFor Needed = omegaNeeded
omegaFor Usable = omegaUsable

runRpoProc ob@(O o oo) solve mkS  cTyp p rpo = f(solve ob (runRP ob mkS cTyp p rpo)) where
  f Nothing = dontKnow (rpoFail p) p
  f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = singleP proof p (setP (restrictTRS dps nondec_dps) p) where

   symbols       = runEvalM bienv $ mapM decodeUsable symbols_raw
   proof         = RPOAFExtraProof decreasingDps usableRules (symbolRes <$> symbols) extraConstraints
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO"
                        ([0..length (rules dps) - 1] \\ nondec_dps)
                        (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR (symbolRes s) | s <- symbols, isUsable s]

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
runRpoProcN ob solve mkS cTyp p rpo = f $ solve ob $ runRP ob mkS cTyp p rpo where
 f Nothing = dontKnow (rpoFail p) p
 f (Just (((non_dec_dps, non_rhsground_dps),ec), bienv, symbols_raw)) =
    let proof         = RPOAFExtraProof decreasingDps usableRules (symbolRes <$> symbols) ec
        symbols       = runEvalM bienv $ mapM decodeUsable symbols_raw
        decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ non_dec_dps) (rules dps)
        usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
        usableSymbols = Set.fromList [ theSymbolR (symbolRes s) | s <- symbols, isUsable s]
        p1            = setP (restrictTRS dps non_dec_dps) p
        p2            = setP (restrictTRS dps non_rhsground_dps) p
    in andP proof p (snub [p1,p2])
       where dps = getP p

{-
proc :: ( Pretty id
        , Info info (RPOProof id), Info info (NarradarProblem typ t)
        , IsDPProblem typ, Monad m
        ) =>
        NarradarProblem typ t -> IO (Maybe ([Int], [RPO.SymbolRes id]))
     -> Proof info m (NarradarProblem typ t)

proc p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (nondec_dps, symbols) ->
                      let proof         = RPOProof decreasingDps [] symbols
                          dps           = getP p
                          decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
                          p'            = setP (restrictTRS dps nondec_dps) p
                          verification  = verifyRPO p symbols nondec_dps
                          isValidProof
                            | isCorrect verification = True
                            | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False
                      in
                         CE.assert isValidProof $
                         singleP proof p p'
-}
-- -------------
-- RPO Proofs
-- -------------

data RPOProof id where
     RPOAFProof :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [SymbolRes id]
                -> RPOProof id

     RPOAFExtraProof
                :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [SymbolRes id]
                -> [Tree (TermN id) Var] -- ^ Extra constraints
                -> RPOProof id
{-
     RPOProof   :: Pretty (Rule t v) =>
                   [Rule t v]       --  ^ Strictly Decreasing dps
                -> [Rule t v]       --  ^ Usable Rules
                -> [RPO.SymbolRes id]
                -> RPOProof id
-}
     RPOFail :: RPOProof id

     deriving Typeable

instance (Ord id, Pretty id) => Eq (RPOProof id) where a == b = pPrint a == pPrint b
instance (Ord id, Pretty id) => Ord (RPOProof id) where compare a b = pPrint a `compare` pPrint b
instance Observable1 RPOProof where observer1 = observeOpaque "RPOProof"
instance Observable a => Observable (RPOProof a) where observer = observer1 ; observers = observers1

rpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> RPOProof (Family.Id t)
rpoFail _ = RPOFail

instance (Ord id, Pretty id) => Pretty (RPOProof id) where
    pPrint (RPOAFProof dps rr ss) = pPrint (RPOAFExtraProof dps rr ss [])
    pPrint (RPOAFExtraProof dps rr ss cc) =
     (if null cc then text "RPO reduction pair"
        else text "RPO reduction pair with the extra constraints" $$
             nest 4 (vcat $ map (printTree 0) cc))
     $$ text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "The argument filtering used was:" $$
        nest 4 (pPrint the_af) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map pPrint rr) $$
        text "Precedence:" <+> printPrec prec theSymbolR ssPrec $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status s of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s <- ssPrec])
     where
       the_af = AF.fromList' [(theSymbolR s, filtering s) | s <- ss]
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
    pPrint RPOFail = text "RPO Reduction Pair : failed to synthetize a suitable ordering"


printPrec f symb    = fsep
                    . punctuate (text " >")
                    . fmap ( fsep
                           . punctuate (text " =")
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)

-- Nil instance

instance (Ord id, Pretty id, HasArity id) => Pretty (RPORuleRemovalProof id) where
    pPrint (RPORuleRemovalProof ex rr ss cc) =
     (if null cc then text "RPO rule removal" -- <+> parens(a <+> text "algebra")
        else text "RPO rule removal with the extra constraints" $$
             nest 4 (vcat $ map (printTree 0) cc))
     $$ text "The following rules are strictly decreasing:" $$
        nest 4 (vcat (map pPrint rr)) $$
        text "Precedence:" <+> printPrec prec theSymbolR ss $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status s of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s <- ss])

    pPrint (RPORuleRemovalFail a) =
      text "RPO rule removal: failed to synthetize a suitable ordering"

