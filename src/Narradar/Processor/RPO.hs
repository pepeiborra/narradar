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
import Data.Bifunctor
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.NarradarTrie (HasTrie)
import Data.Typeable
import Data.List ((\\), groupBy, sortBy, inits)
import Data.Maybe (fromJust)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set

import Narradar.Framework.GraphViz

import Narradar.Types as Narradar hiding (Var)
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.RPO
import Narradar.Constraints.SAT.Solve
import Narradar.Constraints.SAT.RPOAF (SymbolRes, rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, Omega
                                      ,isUsable, theSymbolR, filtering, verifyRPOAF)
--import Narradar.Constraints.SAT.RPO   (verifyRPO)
--import qualified Narradar.Constraints.SAT.RPO as RPO
import qualified Narradar.Constraints.SAT.RPOAF as RPOAF
import Narradar.Utils
import System.IO.Unsafe

-- -------------------
-- RPO SAT Processor
-- -------------------
rpo :: (MonadPlus mp, Info info i, Info info o, Processor info RPOProc i o) =>
       i -> Proof info mp o
rpo = apply (RPOProc RPOSAF MiniSat)

runS FunSat = solveFun
runS FunSatDirect = solveFunDirect
runS (Yices timeout) = unsafePerformIO . solveYicesDirect YicesOpts{maxWeight = 20, timeout = Just 60}
runS (YicesSimp  timeout) = unsafePerformIO . solveYicesSimp YicesOpts{maxWeight = 20, timeout = Just 60}
runS (YicesSimp1 timeout) = unsafePerformIO . solveYicesSimp1 YicesOpts{maxWeight = 20, timeout = Just 60}

data RPOProc   = RPOProc Extension Solver
data Extension = RPOSAF | RPOAF | LPOSAF | MPOAF | LPOAF --  | LPOS | LPO | MPO
data Solver    = Yices Int | YicesSimp Int | YicesSimp1 Int | MiniSat | FunSat | FunSatDirect

instance (Traversable (Problem typ)
         ,Ord id, Show id, Pretty id, HasTrie id, DPSymbol id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ,rpos ~ RPOAF.RPOSsymbol Var id
         ,mpo  ~ RPOAF.MPOsymbol Var id
         ,lpo  ~ RPOAF.LPOsymbol Var id
         ,lpos ~ RPOAF.LPOSsymbol Var id
         ,rpo  ~ RPOAF.RPOsymbol Var id
         ,res  ~ RPOAF.SymbolRes id
         ,Omega typ  rpo
         ,Omega typ  rpos
         ,Omega typ  mpo
         ,Omega typ  lpo
         ,Omega typ  lpos
{-
         ,NUsableRules typ rpo
         ,NUsableRules typ rpos
         ,NUsableRules typ mpo
         ,NUsableRules typ lpo
         ,NUsableRules typ res
-}
--         ,NUsableRules typ res
         ,MkDPProblem typ (NTRS id)
         ,MkDPProblem typ (NTRS rpo)
         ,MkDPProblem typ (NTRS rpos)
         ,MkDPProblem typ (NTRS mpo)
         ,MkDPProblem typ (NTRS lpo)
         ,MkDPProblem typ (NTRS res)
         ,MkDPProblem typ (NTRS lpos)
         ,AF.ApplyAF (NProblem typ res)
         ) => Processor info RPOProc
                             (NProblem typ id)
                             (NProblem typ id)
   where

    apply (RPOProc RPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpo  p)
    apply (RPOProc RPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.rpo  p)
    apply (RPOProc MPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc LPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpos p)

instance (rpos ~ RPOAF.RPOSsymbol Var id
         ,rpo  ~ RPOAF.RPOsymbol Var id
         ,mpo  ~ RPOAF.MPOsymbol Var id
         ,lpo  ~ RPOAF.LPOsymbol Var id
         ,lpos ~ RPOAF.LPOSsymbol Var id
         ,sres ~ RPOAF.SymbolRes id
         ,v    ~ Narradar.Var
         ,Show id, Ord id, Pretty id, DPSymbol id, HasTrie id, Pretty (TermN id)
         ,Info info (RPOProof id)
         ,IsDPProblem base, Pretty base, HasMinimality base
         ,Traversable (Problem base)
         ,Omega (InitialGoal (TermF rpo) base)  rpo
         ,Omega (InitialGoal (TermF rpos) base) rpos
         ,Omega (InitialGoal (TermF mpo) base)  mpo
         ,Omega (InitialGoal (TermF lpos) base) lpos
         ,Omega (InitialGoal (TermF lpo ) base) lpo
         ,NCap base id
         ,NCap base rpos
         ,NCap base rpo
         ,NCap base mpo
         ,NCap base lpo
         ,NCap base lpos
         ,NUsableRules base id
         ,NUsableRules base rpo
         ,NUsableRules base rpos
         ,NUsableRules base mpo
         ,NUsableRules base lpo
         ,NUsableRules base lpos
         ,NeededRules (TermF rpos) v base (NTRS rpos)
         ,NeededRules (TermF rpo)  v base (NTRS rpo)
         ,NeededRules (TermF lpos) v base (NTRS lpos)
         ,NeededRules (TermF lpo)  v base (NTRS lpo)
         ,NeededRules (TermF mpo)  v base (NTRS mpo)
         ,MkDPProblem base (NTRS id)
         ,MkDPProblem base (NTRS rpo)
         ,MkDPProblem base (NTRS rpos)
         ,MkDPProblem base (NTRS mpo)
         ,MkDPProblem base (NTRS lpo)
         ,MkDPProblem base (NTRS lpos)
--         ,NUsableRules base sres
--         ,NCap sres (base, NTRS sres)
         ) => Processor info RPOProc
                             (NProblem (InitialGoal (TermF id) base) id)
                             (NProblem (InitialGoal (TermF id) base) id)
   where

    apply (RPOProc RPOSAF s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.lpos p)
    apply (RPOProc LPOAF  s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.lpo  p)
    apply (RPOProc MPOAF  s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.mpo  p)
    apply (RPOProc RPOAF  s) p = procAF_IG p (runS s $ rpoAF_IGDP True RPOAF.rpo  p)

instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem IRewriting id)
                             (NProblem IRewriting id)
   where
    apply (RPOProc RPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpos p)
    apply (RPOProc LPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.lpo p)
    apply (RPOProc MPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.mpo  p)
    apply (RPOProc RPOAF  s) p = procAF p (runS s $ rpoAF_DP True RPOAF.rpo  p)

instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                             (NProblem Narrowing id)
                             (NProblem Narrowing id)
  where
    apply (RPOProc RPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.mpo  p)
    apply (RPOProc RPOAF  s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.rpo  p)

instance (Ord id, Pretty id, DPSymbol id, Show id, HasTrie id
         ,Info info (RPOProof id)
         ) => Processor info RPOProc
                        (NProblem CNarrowing id)
                        (NProblem CNarrowing id)
  where

    apply (RPOProc RPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.rpos p)
    apply (RPOProc LPOSAF s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.lpos p)
    apply (RPOProc MPOAF  s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.mpo  p)
    apply (RPOProc RPOAF  s) p = procNAF p (runS s $ rpoAF_NDP False RPOAF.rpo  p)


-- -----------------
-- Implementations
-- -----------------

procAF :: (Monad m
          ,sres  ~ SymbolRes id
          ,Info info (NProblem typ id)
          ,Info info (RPOProof id)
          ,Pretty id, Ord id, HasTrie id
          ,Traversable  (Problem typ)
          ,MkDPProblem typ (NTRS id)
          )=> NProblem typ id -> (Maybe ([Int], [SymbolRes id])) -> Proof info m (NProblem typ id)
procAF p Nothing = dontKnow (rpoFail p) p
procAF p (Just (nondec_dps, symbols)) = singleP proof p p'
  where
   proof = RPOAFProof decreasingDps usableRules symbols
   dps   = getP p
   decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
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

procAF_IG p Nothing = dontKnow (rpoFail p) p
procAF_IG p (Just (nondec_dps, symbols)) = singleP proof p (setP (restrictTRS dps nondec_dps) p)
 where
   proof         = RPOAFProof decreasingDps usableRules symbols
   dps           = getP p
   decreasingDps = select ([0..length (rules dps) - 1] \\ nondec_dps) (rules dps)
   usableRules   = [ r | r <- rules(getR p)
                       , let Just f = rootSymbol (lhs r)
                       , f `Set.member` usableSymbols]
   usableSymbols = Set.fromList [ theSymbolR s | s <- symbols, isUsable s]
{-
   verification  = verifyRPOAF typSymbols (getR p) dps symbols nondec_dps
   typSymbols    = mapInitialGoal (bimap convertSymbol id) (getProblemType p)
   convertSymbol = fromJust . (`Map.lookup` Map.fromList [(theSymbolR s, s) | s <- symbols])
   isValidProof
    | isCorrect verification = True
    | otherwise = pprTrace (proof $+$ Ppr.empty $+$ verification) False

 CE.assert isValidProof $
-}


-- For Narrowing we need to add the constraint that one of the dps is ground in the rhs
-- We do not just remove the strictly decreasing pairs,
-- Instead we create two problems, one without the decreasing pairs and one
-- without the ground right hand sides
procNAF p Nothing = dontKnow (rpoFail p) p
procNAF p (Just ((non_dec_dps, non_rhsground_dps), symbols)) =
    let proof = RPOAFProof decreasingDps usableRules symbols
        decreasingDps = select([0..length (rules dps) - 1] \\ non_dec_dps) (rules dps)
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
                -> [RPOAF.SymbolRes id]
                -> RPOProof id
{-
     RPOProof   :: Pretty (Rule t v) =>
                   [Rule t v]       --  ^ Strictly Decreasing dps
                -> [Rule t v]       --  ^ Usable Rules
                -> [RPO.SymbolRes id]
                -> RPOProof id
-}
     RPOFail :: RPOProof id

rpoFail :: Problem typ (NarradarTRS t Narradar.Var) -> RPOProof (TermId t)
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
        text "Precedence:" <+> printPrec RPOAF.precedence RPOAF.theSymbolR ssPrec $$
        text "Status function:" $$
        nest 2 (vcat [text "status" <> parens(pPrint s) <> text "=" <>
                        case status of
                          Mul -> text "MUL"
                          Lex perm -> text "LEX with permutation " <+> pPrint perm
                            | s@RPOAF.SymbolRes{..} <- ss])
     where
       the_af = AF.fromList' [(theSymbolR, filtering) | RPOAF.SymbolRes{..} <- ss]
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