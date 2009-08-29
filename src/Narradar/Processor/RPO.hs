{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
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
import Narradar.Constraints.SAT.RPOAF (rpoAF_NDP, rpoAF_DP, inAF, isUsable, the_symbolR, filtering)
import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe

import qualified Satchmo.Solver.Yices as Yices
import qualified Satchmo.Solver.Yices as MiniSat

-- -------------------
-- RPO SAT Processor
-- -------------------
rpo :: Processor RPOAF trs i o => DPProblem i trs -> Proof (DPProblem o trs)
rpo = apply (RPOAF RPOSAF Yices)


data RPOAF = RPOAF Extension Solver
data Extension = RPOSAF | LPOSAF | MPOAF | LPOAF | LPOS | LPO | MPO
data Solver = Yices | MiniSat -- | Funsat

instance (Ppr id, Ord id) => Processor RPOAF (NarradarTRS id Var) Rewriting  Rewriting  where
    apply (RPOAF RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOAF LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOAF LPOAF Yices)  p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOAF MPOAF Yices)  p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOAF LPOS  Yices)  p = proc   p (Yices.solve $ RPO.lposDP p)
    apply (RPOAF LPO   Yices)  p = proc   p (Yices.solve $ RPO.lpoDP p)
    apply (RPOAF MPO   Yices)  p = proc   p (Yices.solve $ RPO.mpoDP p)

    apply (RPOAF RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOAF LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOAF LPOAF MiniSat)  p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOAF MPOAF MiniSat)  p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOAF LPOS  MiniSat)  p = proc   p (MiniSat.solve $ RPO.lposDP p)
    apply (RPOAF LPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.lpoDP p)
    apply (RPOAF MPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.mpoDP p)

instance (Ppr id, Ord id) => Processor RPOAF (NarradarTRS id Var) IRewriting IRewriting where
    apply (RPOAF RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOAF LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOAF LPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOAF MPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOAF LPOS  Yices)  p = proc   p (Yices.solve $ RPO.lposDP p)
    apply (RPOAF LPO   Yices)  p = proc   p (Yices.solve $ RPO.lpoDP p)
    apply (RPOAF MPO   Yices)  p = proc   p (Yices.solve $ RPO.mpoDP p)

    apply (RPOAF RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOAF LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOAF LPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOAF MPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOAF LPOS  MiniSat)  p = proc   p (MiniSat.solve $ RPO.lposDP p)
    apply (RPOAF LPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.lpoDP p)
    apply (RPOAF MPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.mpoDP p)

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- TODO And also we do not just remove the strictly decreasing pairs,
--      Instead we need to create two problems, one without the decreasing pairs and one
--      without the ground right hand sides
instance (Ppr id, Ord id) => Processor RPOAF (NarradarTRS id Var) Narrowing Narrowing  where
    apply (RPOAF RPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOAF LPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOAF LPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpo  p)
    apply (RPOAF MPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.mpo  p)

    apply (RPOAF RPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOAF LPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOAF LPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpo  p)
    apply (RPOAF MPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.mpo  p)


procAF p m = case unsafePerformIO m of
                  Nothing -> dontKnow RPOFail p
                  Just (dps', symbols) ->
                      let proof = RPOAFProof decreasingDps usableRules symbols
                          decreasingDps = select (rules dps) ([0..length (rules dps)] \\ dps')
                          usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
                          usableSymbols = Set.fromList [ the_symbolR s | s <- symbols, isUsable s]
                          p'            = setP (restrictDPTRS dps dps') p
                      in singleP proof p p'
       where dps = getP p

procNAF p m = case unsafePerformIO m of
                  Nothing -> dontKnow RPOFail p
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
                  Nothing -> dontKnow RPOFail p
                  Just (dps', symbols) ->
                      let proof = RPOProof decreasingDps [] symbols
                          decreasingDps = select (rules dps) ([0..length (rules dps)] \\ dps')
                          p'            = setP (restrictDPTRS dps dps') p
                      in singleP proof p p'
       where dps = getP p

-- -------------
-- RPO Proofs
-- -------------

data RPOAFProof id where RPOAFProof :: Ppr (Rule t v) =>
                                       [Rule t v]             --  ^ Strictly Decreasing dps
                                    -> [Rule t v]       --  ^ Usable Rules
                                    -> [RPOAF.SymbolRes id]
                                    -> RPOAFProof id
                         RPOProof   :: Ppr (Rule t v) =>
                                       [Rule t v]       --  ^ Strictly Decreasing dps
                                    -> [Rule t v]       --  ^ Usable Rules
                                    -> [RPO.SymbolRes id]
                                    -> RPOAFProof id
                         RPOFail :: RPOAFProof ()


instance (Ord id, Ppr id) => Ppr (RPOAFProof id) where
    ppr (RPOAFProof dps rr ss) =
        text "RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map ppr dps)) $$
        text "The argument filtering used was:" $$
        nest 4 (ppr the_af) $$
        text "The usable rules are" $$
        nest 4 (vcat $ map ppr rr) $$
        text "Precedence:" <+> (hsep $ punctuate (text " >") $ map (ppr . the_symbolR) $ sortBy (flip compare) ss) $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(ppr s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> ppr perm
                            | s@RPOAF.SymbolRes{..} <- ss])
     where
       the_af = AF.fromList' [(the_symbolR, filtering) | RPOAF.SymbolRes{..} <- ss]

    ppr (RPOProof dps _ ss) =
        text "Monotonic RPO reduction pair" $$
        text "The following pairs are strictly decreasing:" $$
        nest 4 (vcat (map ppr dps)) $$
        text "Precedence:" <+> (hsep $ punctuate (text " >") $ map (ppr . RPO.the_symbolR) $ sortBy (flip compare) ss) $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(ppr s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> ppr perm
                            | s@RPO.SymbolRes{..} <- ss])

    ppr RPOFail = text "RPO Reduction Pair : failed to synthetize a suitable ordering"

instance (Ord id, Ppr id) => ProofInfo (RPOAFProof id)

-- ----------------------
-- Implementation