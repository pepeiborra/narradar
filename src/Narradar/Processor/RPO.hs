{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Narradar.Processor.RPO where

import Control.Applicative
import Control.Monad
import Data.List ((\\), sortBy, inits)
import qualified Data.Set as Set

import Narradar.Framework.GraphViz

import Narradar.Types
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Constraints.SAT.Common
import Narradar.Constraints.SAT.RPOAF (rpoAF_NDP, rpoAF_DP, inAF, isUsable, the_symbolR, filtering, OmegaUsable)
import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe

import qualified Satchmo.Solver.Yices as Yices
import qualified Satchmo.Solver.Minisat as MiniSat

-- -------------------
-- RPO SAT Processor
-- -------------------
rpo :: (MonadPlus mp, Info info i, Info info o, Processor info RPOProc i o) =>
       i -> Proof info mp o
rpo = apply (RPOProc RPOSAF MiniSat)


data RPOProc = RPOProc Extension Solver
data Extension = RPOSAF | LPOSAF | MPOAF | LPOAF | LPOS | LPO | MPO
data Solver = Yices | MiniSat -- | Funsat

instance (Ord id, Pretty id
         ,Info info (RPOProof id)
         ) =>
    Processor info RPOProc
                  (DPProblem Rewriting  (NarradarTRS (TermF id) Var))
                  (DPProblem Rewriting  (NarradarTRS (TermF id) Var))
   where
    apply (RPOProc RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF Yices)  p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOProc MPOAF Yices)  p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  Yices)  p = proc   p (Yices.solve $ RPO.lposDP p)
    apply (RPOProc LPO   Yices)  p = proc   p (Yices.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   Yices)  p = proc   p (Yices.solve $ RPO.mpoDP p)

    apply (RPOProc RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF MiniSat)  p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOProc MPOAF MiniSat)  p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  MiniSat)  p = proc   p (MiniSat.solve $ RPO.lposDP p)
    apply (RPOProc LPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.mpoDP p)

instance (Ord id, Pretty id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (DPProblem IRewriting (NarradarTRS (TermF id) Var))
                             (DPProblem IRewriting  (NarradarTRS (TermF id) Var))
   where
    apply (RPOProc RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOProc MPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  Yices)  p = proc   p (Yices.solve $ RPO.lposDP p)
    apply (RPOProc LPO   Yices)  p = proc   p (Yices.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   Yices)  p = proc   p (Yices.solve $ RPO.mpoDP p)

    apply (RPOProc RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOProc MPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  MiniSat)  p = proc   p (MiniSat.solve $ RPO.lposDP p)
    apply (RPOProc LPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.mpoDP p)

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- TODO And also we do not just remove the strictly decreasing pairs,
--      Instead we need to create two problems, one without the decreasing pairs and one
--      without the ground right hand sides
instance (Ord id, Pretty id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (DPProblem Narrowing (NarradarTRS (TermF id) Var))
                             (DPProblem Narrowing (NarradarTRS (TermF id) Var))
  where
    apply (RPOProc RPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpo  p)
    apply (RPOProc MPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.mpo  p)

    apply (RPOProc RPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpo  p)
    apply (RPOProc MPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.mpo  p)

instance (Ord id, Pretty id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                        (DPProblem CNarrowing (NarradarTRS (TermF id) Var))
                        (DPProblem CNarrowing (NarradarTRS (TermF id) Var))
  where
    apply (RPOProc RPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpo  p)
    apply (RPOProc MPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.mpo  p)

    apply (RPOProc RPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc LPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpo  p)
    apply (RPOProc MPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.mpo  p)


procAF p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (dps', symbols) ->
                      let proof = RPOAFProof decreasingDps usableRules symbols
                          decreasingDps = select (rules dps) ([0..length (rules dps)] \\ dps')
                          usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
                          usableSymbols = Set.fromList [ the_symbolR s | s <- symbols, isUsable s]
                          p'            = setP (restrictDPTRS dps dps') p
                      in singleP proof p p'
       where dps = getP p

procNAF p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just ((non_dec_dps, non_rhsground_dps), symbols) ->
                      let proof = RPOAFProof decreasingDps usableRules symbols
                          decreasingDps = select (rules dps) ([0..length (rules dps)] \\ non_dec_dps)
                          usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
                          usableSymbols = Set.fromList [ the_symbolR s | s <- symbols, isUsable s]
                          p1            = setP (restrictDPTRS dps non_dec_dps) p
                          p2            = setP (restrictDPTRS dps non_rhsground_dps) p
                      in andP proof p (snub [p1,p2])
       where dps = getP p

proc p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (dps', symbols) ->
                      let proof = RPOProof decreasingDps [] symbols
                          decreasingDps = select (rules dps) ([0..length (rules dps)] \\ dps')
                          p'            = setP (restrictDPTRS dps dps') p
                      in singleP proof p p'
       where dps = getP p

-- -------------
-- RPO Proofs
-- -------------

data RPOProof id where
     RPOAFProof :: Pretty (Rule t v) =>
                   [Rule t v]       --  ^ Strictly Decreasing dps
                -> [Rule t v]       --  ^ Usable Rules
                -> [RPOAF.SymbolRes id]
                -> RPOProof id
     RPOProof   :: Pretty (Rule t v) =>
                   [Rule t v]       --  ^ Strictly Decreasing dps
                -> [Rule t v]       --  ^ Usable Rules
                -> [RPO.SymbolRes id]
                -> RPOProof id
     RPOFail :: RPOProof id

rpoFail :: DPProblem typ (NTRS id Var) -> RPOProof id
rpoFail _ = RPOFail

instance (Ord id, Pretty id) => Pretty (RPOProof id) where
    pPrint (RPOAFProof dps rr ss) =
        text "RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "The argument filtering used was:" $$
        nest 4 (pPrint the_af) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map pPrint rr) $$
        text "Precedence:" <+> (hsep $ punctuate (text " >") $ map (pPrint . the_symbolR) $ sortBy (flip compare) ss) $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPOAF.SymbolRes{..} <- ss])
     where
       the_af = AF.fromList' [(the_symbolR, filtering) | RPOAF.SymbolRes{..} <- ss]

    pPrint (RPOProof dps _ ss) =
        text "Monotonic RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map pPrint dps)) $$
        text "Precedence:" <+> (hsep $ punctuate (text " >") $ map (pPrint . RPO.the_symbolR) $ sortBy (flip compare) ss) $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPO.SymbolRes{..} <- ss])

    pPrint RPOFail = text "RPO Reduction Pair : failed to synthetize a suitable ordering"


-- ----------------------
-- Implementation