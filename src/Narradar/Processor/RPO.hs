{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Narradar.Processor.RPO where

import Control.Applicative
import Control.Exception as CE (assert)
import Control.Monad
import Data.Foldable (Foldable)
import Data.Typeable
import Data.Traversable (Traversable)
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Narradar.Framework.GraphViz

import Narradar.Types
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.SAT.Common
import Narradar.Constraints.SAT.RPOAF (SymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, Omega, inAF, isUsable, the_symbolR, filtering, verifyRPOAF)
import Narradar.Constraints.SAT.RPO   (verifyRPO)
import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe

import qualified Satchmo.Solver.Yices as Yices
-- import qualified Satchmo.Solver.Minisat as MiniSat

-- -------------------
-- RPO SAT Processor
-- -------------------
rpo :: (MonadPlus mp, Info info i, Info info o, Processor info RPOProc i o) =>
       i -> Proof info mp o
rpo = apply (RPOProc RPOSAF MiniSat)


runS (Yices timeout) = Yices.solveW (Just timeout) 20

data RPOProc   = RPOProc Extension Solver
data Extension = RPOSAF | LPOSAF | MPOAF | LPOAF  | LPOS | LPO | MPO
data Solver    = Yices Int | MiniSat -- FunSat

instance (Traversable (Problem typ)
         ,Ord id, Show id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ,rpo  ~ RPOAF.Symbol id
         ,mpo  ~ RPOAF.MPOsymbol id
         ,lpo  ~ RPOAF.LPOsymbol id
         ,lpos ~ RPOAF.LPOSsymbol id
         ,res  ~ RPO.SymbolRes id
         ,res' ~ RPOAF.SymbolRes id
         ,Omega typ (TermF rpo)
         ,Omega typ (TermF mpo)
         ,Omega typ (TermF lpo)
         ,Omega typ (TermF lpos)
         ,NUsableRules typ rpo
         ,NUsableRules typ mpo
         ,NUsableRules typ lpo
         ,NUsableRules typ lpos
         ,NUsableRules typ res
         ,NUsableRules typ res'
         ,MkDPProblem typ (NTRS id)
         ,MkDPProblem typ (NTRS rpo)
         ,MkDPProblem typ (NTRS mpo)
         ,MkDPProblem typ (NTRS lpo)
         ,MkDPProblem typ (NTRS lpos)
         ,MkDPProblem typ (NTRS res)
         ,MkDPProblem typ (NTRS res')
         ,AF.ApplyAF (NProblem typ res')
         ) => Processor info RPOProc
                             (NProblem typ id)
                             (NProblem typ id)
   where

    apply (RPOProc RPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOProc MPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS   s)  p = proc   p (runS s $ RPO.lposDP p)
    apply (RPOProc LPO    s)  p = proc   p (runS s $ RPO.lpoDP p)
    apply (RPOProc MPO    s)  p = proc   p (runS s $ RPO.mpoDP p)

instance (rpo  ~ RPOAF.Symbol id
         ,mpo  ~ RPOAF.MPOsymbol id
         ,lpo  ~ RPOAF.LPOsymbol id
         ,lpos ~ RPOAF.LPOSsymbol id
         ,sres ~ RPOAF.SymbolRes id
         ,Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ,IsDPProblem base, Pretty base, Traversable (Problem base)
         ,Omega (InitialGoal (TermF rpo) base) (TermF rpo)
         ,Omega (InitialGoal (TermF mpo) base) (TermF mpo)
         ,Omega (InitialGoal (TermF lpos) base) (TermF lpos)
         ,Omega (InitialGoal (TermF lpo ) base) (TermF lpo )
         ,HasSignature (NProblem base id), id ~ SignatureId (NProblem base id)
         ,HasSignature (NProblem base rpo),  RPOAF.Symbol id ~ SignatureId (NProblem base rpo)
         ,HasSignature (NProblem  base mpo),  RPOAF.MPOsymbol id ~ SignatureId (NProblem base mpo)
         ,HasSignature (NProblem  base lpo ), RPOAF.LPOsymbol id ~ SignatureId (NProblem base lpo )
         ,HasSignature (NProblem  base lpos), RPOAF.LPOSsymbol id ~ SignatureId (NProblem base lpos)
         ,NCap id   (base, NTRS id)
         ,NCap rpo  (base, NTRS rpo)
         ,NCap mpo  (base, NTRS mpo)
         ,NCap lpo  (base, NTRS lpo)
         ,NCap lpos (base, NTRS lpos)
         ,NUsableRules base id
         ,NUsableRules base rpo
         ,NUsableRules base mpo
         ,NUsableRules base lpo
         ,NUsableRules base lpos
         ,MkDPProblem base (NTRS id)
         ,MkDPProblem base (NTRS rpo)
         ,MkDPProblem base (NTRS mpo)
         ,MkDPProblem base (NTRS lpo)
         ,MkDPProblem base (NTRS lpos)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) base) id)
                             (NProblem (InitialGoal (TermF id) base) id)
   where

    apply (RPOProc RPOSAF s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOAF  s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.lpo  p)
    apply (RPOProc MPOAF  s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.mpo  p)

instance (Ord id, Pretty id, Show id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (Problem IRewriting (NarradarTRS (TermF id) Var))
                             (Problem IRewriting  (NarradarTRS (TermF id) Var))
   where
    apply (RPOProc RPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpo p)
    apply (RPOProc MPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOS  s)  p = proc   p (runS s $ RPO.lposDP p)
    apply (RPOProc LPO   s)  p = proc   p (runS s $ RPO.lpoDP p)
    apply (RPOProc MPO   s)  p = proc   p (runS s $ RPO.mpoDP p)

instance (Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem Narrowing id)
                             (NProblem Narrowing id)
  where
    apply (RPOProc RPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.mpo  p)

instance (Ord id, Pretty id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                        (Problem CNarrowing (NarradarTRS (TermF id) Var))
                        (Problem CNarrowing (NarradarTRS (TermF id) Var))
  where

    apply (RPOProc RPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.mpo  p)

-- Liftings


instance ( Processor info RPOProc (Problem base trs) (Problem base trs)
         , Info info (Problem base trs)
         )=> Processor info RPOProc (Problem (InitialGoal t base) trs) (Problem (InitialGoal t base) trs)
  where
   apply = liftProcessor


-- -----------------
-- Implementations
-- -----------------

procAF :: (Monad m
          ,sres  ~ SymbolRes id
          ,Info info (NProblem typ id)
          ,Info info (RPOProof id)
          ,Pretty id, Ord id
          ,HasSignature (NProblem typ sres), SignatureId (NProblem typ sres) ~ SymbolRes id
          ,Traversable  (Problem typ)
          ,MkDPProblem typ (NTRS sres)
          ,MkDPProblem typ (NTRS id)
          ,NUsableRules typ sres
          ,AF.ApplyAF (NProblem typ sres)
          )=> NProblem typ id -> (IO (Maybe ([Int], [SymbolRes id]))) -> Proof info m (NProblem typ id)
procAF p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (nondec_dps, symbols) ->
                      let proof = RPOAFProof decreasingDps usableRules symbols
                          decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
                          usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
                          usableSymbols = Set.fromList [ the_symbolR s | s <- symbols, isUsable s]
                          p'            = setP (restrictTRS dps nondec_dps) p
                          verification  = verifyRPOAF p symbols nondec_dps
                          isValidProof
                            | isCorrect verification = True
                            | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False
                      in
                         CE.assert isValidProof $
                         singleP proof p p'
       where dps = getP p


procAF_IG p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just (nondec_dps, symbols) ->
                      let proof = RPOAFProof decreasingDps usableRules symbols
                          decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
                          usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
                          usableSymbols = Set.fromList [ the_symbolR s | s <- symbols, isUsable s]
                          p'            = setP (restrictTRS dps nondec_dps) p

                      in
                         singleP proof p p'
       where dps = getP p

-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
procNAF p m = case unsafePerformIO m of
                  Nothing -> dontKnow (rpoFail p) p
                  Just ((non_dec_dps, non_rhsground_dps), symbols) ->
                      let proof = RPOAFProof decreasingDps usableRules symbols
                          decreasingDps = select([0..length (rules dps) - 1] \\ non_dec_dps) (rules dps)
                          usableRules   = [ r | r <- rules(getR p), let Just f = rootSymbol (lhs r), f `Set.member` usableSymbols]
                          usableSymbols = Set.fromList [ the_symbolR s | s <- symbols, isUsable s]
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
-}
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


printPrec f symb    = fsep
                    . punctuate (text " >")
                    . fmap ( fsep
                           . punctuate (text (" ="))
                           . fmap (pPrint . symb))
                    . groupBy ((==) `on` f)
                    . sortBy (flip compare `on` f)