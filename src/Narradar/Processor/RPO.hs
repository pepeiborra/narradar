{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
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

module Narradar.Processor.RPO where

import Control.Applicative
import Control.DeepSeq
import Control.Exception as CE (assert)
import Control.Monad
import Control.Parallel.Strategies
import Data.Bifunctor
import Data.Foldable as F (Foldable, toList)
import Data.Traversable (Traversable)
import Data.Hashable
import Data.Suitable (Suitable)
import Data.Typeable
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import Data.Monoid (Monoid(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Term.Family as Family
import Prelude.Extras

import Narradar.Framework.GraphViz

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO (Status(..))
import Narradar.Constraints.SAT.MonadSAT( Decode(..),Tree,printTree, mapTreeTerms,EvalM, Var, BIEnv)
import qualified Narradar.Constraints.SAT.MonadSAT as MonadSAT
import Narradar.Constraints.SAT.RPOAF ( UsableSymbol(..), MkSATSymbol
                                      , RPOSsymbol(..), RPOsymbol(..), LPOSsymbol, LPOsymbol, MPOsymbol
                                      , RPOProblemN, RPOId
                                      , UsableSymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, rpoAF_IGDP'
                                      , theSymbolR, isUsable, usableSymbol, filtering, status
                                      , verifyRPOAF, isCorrect
                                      , omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone)

import Funsat.TermCircuit (runEvalM)

import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe
import qualified Debug.Trace
import qualified Funsat.TermCircuit as RPOAF

import Debug.Hoed.Observe

type AllowCol = Bool
data RPOProc (info :: * -> *) where
  RPOProc :: Extension -> UsableRulesMode -> AllowCol -> RPOProc info
type instance InfoConstraint (RPOProc info) = info

instance Observable (RPOProc info) where observer = observeOpaque "RPO processor"

{-
  Some combinations are not safe. The ones I am aware of right now:
   - Existentials are only safe in the SMTFFI backed. Therefore:
   - SMTSerial cannot do MPO because the MPO encoding uses existentials
   - Some of the LPOS encodings have existentials disabled. Ideally we
   - would enable them only in the FFI encoding

 -}
data Extension       = RPOSAF | RPOAF | LPOSAF | LPOAF | MPOAF
data UsableRulesMode = None | Usable | Needed

procAF' p ur run = fmap (mapFramework getConstant) $ procAF (mapFramework Constant p) ur run

procAF p usablerules run = (f . unsafePerformIO . run omega) p
 where
  omega = case usablerules of
            Needed -> omegaNeeded
            Usable -> omegaUsable
            None   -> omegaNone

  f Nothing = dontKnow (rpoFail p) p
  f (Just (nondec_dps, bienv, symbols_raw)) = singleP proof p p'
   where
    symbols       = runEvalM bienv $ mapM decode symbols_raw
    proof         = RPOAFProof decreasingDps usableRules symbols
    dps           = getP p
    decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
    usableRules   = [ r | r <- rules(getR p)
                        , let Just f = rootSymbol (lhs r)
                        , f `Set.member` usableSymbols]
    usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
    p'            = setP (restrictTRS dps nondec_dps) p

{-
   verification  = forDPProblem verifyRPOAF p symbols nondec_dps
   isValidProof
     | isCorrect verification = True
     | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False

   CE.assert isValidProof $
-}
{-
procAF_IG ::
  forall info typ base id sid repr e a m .
                ( Decode a (UsableSymbolRes sid)
                , FrameworkProblemN typ sid
                , RPOId id
                , ExpandDPair (InitialGoal (TermF id) base) (NTRS id)
                , ExpandDPair base (NTRS id)
                , InsertDPairs (InitialGoal (TermF id) base) (NTRS id)
                , InsertDPairs base (NTRS id)
                , PprTPDB (NProblem base id)
                , Suitable info (RPOProof sid)
                , Suitable info (NProblem typ sid)
                , Applicative info, Ord1 info, Typeable info
                , Monad m
                , Family.Var id  ~ Var
                , Family.TermF repr ~ TermF id
                , RPOAF.CoRPO repr (TermF id) Narradar.Var Var
                , RPOAF.RPOExtCircuit repr id
                , MonadSAT.ECircuit repr
                ) => NProblem typ sid
                  -> SExtension e
                  -> UsableRulesMode
                  -> ((NProblem (InitialGoal (TermF id) base) id
                       -> (repr Var, EvalM Var [Tree (TermN id) Var]))
                       -> NProblem typ sid
                       -> IO (Maybe (([Int], [Tree (TermN sid) Var]), BIEnv (Family.Var a), [a])))
                  -> Proof info m (NProblem typ sid)
-}
procAF_IG p usablerules run = (f . unsafePerformIO . run omega) p where
 omega = case usablerules of
            Needed -> omegaIG
            Usable -> omegaIG
--            None   -> omegaNone

 f Nothing = dontKnow (rpoFail p) p
 f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p)
  where
   symbols       = runEvalM bienv $ mapM decode symbols_raw
   proof         = RPOAFProof decreasingDps usableRules symbols
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
{-
   verification  = runEvalM bienv $ verifyRPOAF typSymbols rrSymbols dpsSymbols nondec_dps
   typSymbols    = mapInitialGoal (bimap convertSymbol id) (getProblemType p)
   rrSymbols     = mapNarradarTRS (mapTermSymbols convertSymbol) (getR p)
   dpsSymbols    = mapNarradarTRS (mapTermSymbols convertSymbol) (getP p)
   convertSymbol = fromJust . (`Map.lookup` Map.fromList
                                            [(theSymbolR(runEvalM bienv $ decode s), s)
                                                 | s <- symbols_raw])
   isValidProof
    | isCorrect verification = True
    | otherwise = Debug.Trace.trace (show (proof $+$ Ppr.empty $+$ verification)) False
-}

procAF_IGgen ::
  forall info typ base id sid m e .
                ( Decode id (UsableSymbolRes sid)
                , FrameworkProblemN typ sid
                , RPOId id, GenSymbol id
                , ExpandDPair (InitialGoal (TermF id) base) (NTRS id)
                , ExpandDPair base (NTRS id)
                , InsertDPairs (InitialGoal (TermF id) base) (NTRS id)
                , InsertDPairs base (NTRS id)
                , PprTPDB (NProblem base id)
                , Suitable info (RPOProof sid)
                , Suitable info (NProblem typ sid)
                , Applicative info, Ord1 info, Typeable info
                , Monad m
                , Family.Var id  ~ Var
                ) => NProblem typ sid
                  -> UsableRulesMode
                  -> ((NProblem (InitialGoal (TermF id) base) id
                            -> (Tree (TermN id) Var, EvalM Var [Tree (TermN id) Var]))
                       -> NProblem typ sid
                       -> IO (Maybe (([Int], [Tree (TermN sid) Var]), BIEnv Var, [id])))
                  -> Proof info m (NProblem typ sid)

procAF_IGgen p usablerules run = (f . unsafePerformIO . run omega) p where
  omega = case usablerules of
            Needed -> omegaIGgen
            Usable -> omegaIGgen
--            None   -> omegaNone
  f Nothing = dontKnow (rpoFail p) p
  f (Just ((nondec_dps, extraConstraints), bienv, symbols_raw))
   = -- CE.assert isValidProof $
     singleP proof p (setP (restrictTRS dps nondec_dps) p) where

   symbols       = runEvalM bienv $ mapM decode (symbols_raw)
   proof         = RPOAFExtraProof decreasingDps usableRules symbols extraConstraints'
   dps           = getP p
   decreasingDps = selectSafe "Narradar.Processor.RPO"
                        ([0..length (rules dps) - 1] \\ nondec_dps)
                        (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
   extraConstraints' :: [Tree (TermN sid) Var]
   extraConstraints' = mapTreeTerms (mapTermSymbols id) <$> extraConstraints

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
procNAF p usablerules run =
 case usablerules of
            Needed -> (f . unsafePerformIO . run omegaNeeded) p
            Usable -> (f . unsafePerformIO . run omegaUsable) p
            None   -> (f . unsafePerformIO . run omegaNone) p
   where
 f Nothing = dontKnow (rpoFail p) p
 f (Just ((non_dec_dps, non_rhsground_dps), bienv, symbols_raw)) =
    let proof = RPOAFProof decreasingDps usableRules symbols
        symbols       = runEvalM bienv $ mapM decode (symbols_raw)
        decreasingDps = selectSafe "Narradar.Processor.RPO" ([0..length (rules dps) - 1] \\ non_dec_dps) (rules dps)
        usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
        usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
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
                -> [UsableSymbolRes id]
                -> RPOProof id

     RPOAFExtraProof
                :: Pretty (RuleN id) =>
                   [RuleN id]       --  ^ Strictly Decreasing dps
                -> [RuleN id]       --  ^ Usable Rules
                -> [UsableSymbolRes id]
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
        text "Precedence:" <+> printPrec RPOAF.prec theSymbolR ssPrec $$
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
                           . punctuate (text (" ="))
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)

-- Nil instance
instance Ord a => RemovePrologId (RPOAF.Usable a) where
  type WithoutPrologId (RPOAF.Usable a) = RPOAF.Usable a
  removePrologId = Just
