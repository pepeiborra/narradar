{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Narradar.Processor.RPO where

import Control.Applicative
import Control.Monad
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.List ((\\), groupBy, sortBy, inits)
import qualified Data.Set as Set

import Narradar.Framework.GraphViz

import Narradar.Types
import Narradar.Types.Problem.NarrowingGen
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Constraints.SAT.Common
import Narradar.Constraints.SAT.RPOAF (rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, inAF, isUsable, the_symbolR, filtering)
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


data RPOProc   = RPOProc Extension Solver
data Extension = RPOSAF | LPOSAF | MPOAF  | LPOS | LPO | MPO
data Solver    = Yices | MiniSat -- | Funsat

instance (Traversable (Problem typ)
         ,rpo  ~ RPOAF.Symbol id
         ,mpo  ~ RPOAF.MPOsymbol id
         ,lpos ~ RPOAF.LPOSsymbol id
         ,Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ,NUsableRules rpo  (typ, NTRS rpo, NTRS rpo)
         ,NUsableRules mpo  (typ, NTRS mpo, NTRS mpo)
         ,NUsableRules lpos (typ, NTRS lpos, NTRS lpos)
         ,HasSignature (NProblem typ id), id ~ SignatureId (NProblem typ id)
         ,HasSignature (NProblem typ rpo),  rpo  ~ SignatureId (NProblem typ rpo)
         ,HasSignature (NProblem typ mpo),  mpo  ~ SignatureId (NProblem typ mpo)
         ,HasSignature (NProblem typ lpos), lpos ~ SignatureId (NProblem typ lpos)
         ,MkDPProblem typ (NTRS id)
         ,MkDPProblem typ (NTRS rpo)
         ,MkDPProblem typ (NTRS mpo)
         ,MkDPProblem typ (NTRS lpos)
         ) => Processor info RPOProc
                             (NProblem typ id)
                             (NProblem typ id)
   where
    apply (RPOProc RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc MPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  Yices)  p = proc   p (Yices.solve $ RPO.lposDP p)
    apply (RPOProc LPO   Yices)  p = proc   p (Yices.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   Yices)  p = proc   p (Yices.solve $ RPO.mpoDP p)

    apply (RPOProc RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc MPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  MiniSat)  p = proc   p (MiniSat.solve $ RPO.lposDP p)
    apply (RPOProc LPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.mpoDP p)

instance (rpo  ~ RPOAF.Symbol id
         ,mpo  ~ RPOAF.MPOsymbol id
         ,lpos ~ RPOAF.LPOSsymbol id
         ,Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ,IsDPProblem base, Pretty base, Traversable (Problem base)
         ,HasSignature (NProblem base id), id ~ SignatureId (NProblem base id)
         ,HasSignature (NProblem base rpo),  RPOAF.Symbol id ~ SignatureId (NProblem base rpo)
         ,HasSignature (NProblem  base mpo),  RPOAF.MPOsymbol id ~ SignatureId (NProblem base mpo)
         ,HasSignature (NProblem  base lpos), RPOAF.LPOSsymbol id ~ SignatureId (NProblem base lpos)
         ,NCap id   (base, NTRS id)
         ,NCap rpo  (base, NTRS rpo)
         ,NCap mpo  (base, NTRS mpo)
         ,NCap lpos (base, NTRS lpos)
         ,NUsableRules id   (base, NTRS id,  NTRS id)
         ,NUsableRules rpo  (base, NTRS rpo, NTRS rpo)
         ,NUsableRules mpo  (base, NTRS mpo, NTRS mpo)
         ,NUsableRules lpos (base, NTRS lpos, NTRS lpos)
         ,MkDPProblem base (NTRS id)
         ,MkDPProblem base (NTRS rpo)
         ,MkDPProblem base (NTRS mpo)
         ,MkDPProblem base (NTRS lpos)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) base) id)
                             (NProblem (InitialGoal (TermF id) base) id)
   where
    apply (RPOProc RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc MPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_IGDP True RPOAF.mpo  p)

    apply (RPOProc RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc MPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_IGDP True RPOAF.mpo  p)


{-
instance (Ord id, Pretty id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (Problem IRewriting (NarradarTRS (TermF id) Var))
                             (Problem IRewriting  (NarradarTRS (TermF id) Var))
   where
    apply (RPOProc RPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc MPOAF  Yices) p = procAF p (Yices.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  Yices)  p = proc   p (Yices.solve $ RPO.lposDP p)
    apply (RPOProc LPO   Yices)  p = proc   p (Yices.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   Yices)  p = proc   p (Yices.solve $ RPO.mpoDP p)

    apply (RPOProc RPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc MPOAF  MiniSat) p = procAF p (MiniSat.solve $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  MiniSat)  p = proc   p (MiniSat.solve $ RPO.lposDP p)
    apply (RPOProc LPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.lpoDP p)
    apply (RPOProc MPO   MiniSat)  p = proc   p (MiniSat.solve $ RPO.mpoDP p)
-}


instance (Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem Narrowing id)
                             (NProblem Narrowing id)
  where
    apply (RPOProc RPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.mpo  p)

    apply (RPOProc RPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.mpo  p)

instance (Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                        (Problem CNarrowing (NarradarTRS (TermF id) Var))
                        (Problem CNarrowing (NarradarTRS (TermF id) Var))
  where
    apply (RPOProc RPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  Yices) p = procNAF p (Yices.solve $ rpoAF_NDP False RPOAF.mpo  p)

    apply (RPOProc RPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  MiniSat) p = procNAF p (MiniSat.solve $ rpoAF_NDP False RPOAF.mpo  p)

-- Liftings


instance ( Processor info RPOProc (Problem base trs) (Problem base trs)
         , Info info (Problem base trs)
         )=> Processor info RPOProc (Problem (InitialGoal t base) trs) (Problem (InitialGoal t base) trs)
  where
   apply = liftProcessor


-- -----------------
-- Implementations
-- -----------------

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

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
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
{-
proc :: ( Pretty id
        , Info info (RPOProof id), Info info (NarradarProblem typ t)
        , IsDPProblem typ, Monad m
        ) =>
        NarradarProblem typ t -> IO (Maybe ([Int], [RPO.SymbolRes id]))
     -> Proof info m (NarradarProblem typ t)
-}
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

rpoFail :: Problem typ (NarradarTRS t Var) -> RPOProof (TermId t)
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
        text "Precedence:" <+> printPrec RPOAF.precedence RPOAF.the_symbolR ss $$
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
        text "Precedence:" <+> printPrec RPO.precedence RPO.the_symbolR ss $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPO.SymbolRes{..} <- ss])

    pPrint RPOFail = text "RPO Reduction Pair : failed to synthetize a suitable ordering"


printPrec f symb    = hsep
                    . punctuate (text " >")
                    . fmap ( hsep
                           . punctuate (text (" ="))
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)