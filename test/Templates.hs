{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Templates where

import Control.Monad.Reader (ask)
import Data.Foldable (toList)
import Data.Maybe (fromJust,isJust)
import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Debug.Trace

import qualified Data.Map as Map

import Narradar.Types as Narradar
import Narradar.Constraints.SAT.MonadSAT as SAT
import Narradar.Constraints.SAT.RPOAF (SymbolRes)
import Narradar.Constraints.SAT.Solve
import Narradar.Constraints.SAT.YicesCircuit (YicesSource)
import qualified Narradar.Constraints.SAT.YicesFFICircuit as FFI (YicesSource)

import Funsat.RPOCircuit

import qualified Funsat.ECircuit as EC
import Narradar.Constraints.SAT.RPOAF (rpos)
import Narradar.Constraints.SAT.RPOAF.Symbols
import Control.Monad(liftM)

import Generators
import Types

--instance AssertCircuit (Shared term) where assertCircuit = (/\)
-- prop_ecircuitToCnf_direct_yices = mkYicesDirectProp (undefined :: Proxy LDPId) (sizedECircuit :: SizedGen (EC.Tree SAT.Var))
-- prop_rposrulesEqToCNF_direct_smtFFI :: [RuleN RandId] -> Property
-- prop_rposrulesEqToCNF_direct_smtFFI = mkRuleEqProp (smtFFISolverRPOS)
--prop_rposrulesEqToCNF_simp1_yices :: [RuleN RandId] -> Property
--prop_rposrulesEqToCNF_simp1_yices   = mkRuleEqProp  satYicesSimpSolverRPOS
--prop_lpocircuitToCnf_direct_yices = mkYicesDirectRPOProp (undefined :: Proxy LDPId) (liftM fst . sizedLPOCircuit :: SizedGen (Tree (TermN LDPId) SAT.Var))

-- --------------------------
-- Correctness of SAT solvers
-- --------------------------

yicesOpts = YicesOpts 0 (Just 5)

mkTypeCheckProp :: forall repr term id v .
                       (Enum v, Ord v, Show v, Hashable v
                       ,Show term, Show (repr  v)
                       ,CastCircuit repr (Tree term)
                       ,CastCo repr (Tree term) v
                       ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ) => Proxy id -> ShrinkableSizedGen (repr v, Int) -> Property
mkTypeCheckProp _ (shrink,gen) = forAllShrink (sized gen) shrink $ \(c,pool) ->
                                 isJust(typeCheckTree (castCircuit c :: Tree term v))

mkYicesProp :: forall id v repr .
                       (Ord id, Show id, Hashable id
                       ,Enum v, Ord v, Show v, Hashable v
                     ,Show (repr v)
                     ,CastCircuit repr (Shared (TermN id))
                     ,CastCircuit repr Eval
                     ,CastCo repr (Shared (TermN id)) v
                     ,CastCo repr Eval v
                       ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ,RPOExtCircuit (Shared (TermN id)) (TermN id)
                       ) => Proxy id -> ShrinkableSizedGen (repr v, Int) -> Property
mkYicesProp _ (shrink,gen) = forAllShrink (sized gen) shrink $ \(c , pool) ->
    let correct = unsafePerformIO $
                  satYices' pool yicesOpts
                    (assert [castCircuit c :: Shared (TermN id) v] >>
                     return (evalB (castCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimpProp :: forall id v repr .
                       (Ord id, Show id, Hashable id
                       ,Enum v, Ord v, Show v, Hashable v
                     ,Show (repr v)
                     ,CastCircuit repr (Shared (TermN id))
                     ,CastCircuit repr Eval
                     ,CastCo repr (Shared (TermN id)) v
                     ,CastCo repr Eval v
                       ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ,RPOExtCircuit (Shared (TermN id)) (TermN id)
                       ) => Proxy id -> SizedGen (repr v, Int) -> Property
mkYicesSimpProp _ gen = forAll (sized gen) $ \(c , pool) ->
    let correct = unsafePerformIO $
                  satYicesSimp' pool yicesOpts
                    (assert [castCircuit c :: Shared (TermN id) v] >>
                     return (evalB (castCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x


mkSMTProp :: forall id v repr.
                      ( Ord id, Show id, Pretty id, Hashable id
                      , Enum v, Ord v, Show v, Hashable v
                      , Show (repr v)
                      , CastCircuit repr (FFI.YicesSource id)
                      , CastCircuit repr Eval
                      , CastCo repr (FFI.YicesSource id) v
                      , CastCo repr Eval v
                      , HasPrecedence v id, HasFiltering v id, HasStatus v id
                      , RPOExtCircuit (FFI.YicesSource id) (TermN id)
                      ) => Proxy id -> ShrinkableSizedGen (repr v, Int) -> Property
mkSMTProp _ (shrink,gen) = forAllShrink (sized gen) shrink $ \(c,pool) ->
    let correct = unsafePerformIO $
                  smtFFI' pool
                  (assert [castCircuit c :: FFI.YicesSource id v]  >>
                     return (evalB (castCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

-- ----------------------------
-- Correctness of RPO orderings
-- ----------------------------

data ExistSolver symb repr =
    forall id m .
    ( RPOCircuit repr (TermN (symb SAT.Var id))
    , CoRPO repr (TermN (symb SAT.Var id)) SAT.Var
    , MonadSAT repr SAT.Var m
    ) => ExistSolver (SymbolFactory symb) (forall a. m (EvalM SAT.Var a) -> Maybe a)

--type ExistSolver symb = forall a. (SAT (TermN(symb SAT.Var DPRandId)) SAT.Var (EvalM SAT.Var a)) -> Maybe a

mkSymbolRules :: (MonadSAT repr SAT.Var m, Co repr SAT.Var) => SymbolFactory symb -> [RuleN RandId] -> m [RuleN (symb SAT.Var DPRandId)]
mkSymbolRules ext rr = do
     let symbols = toList $ getAllSymbols rr
     symbols'   <- mapM (mkSATSymbol ext) symbols
     let convert = fromJust . (`Map.lookup` dict)
         dict    = Map.fromList (zip symbols symbols')
         rr_s    = (fmap.fmap) (mapTermSymbols convert) rr
     return rr_s


mkRuleGtProp, mkRuleEqProp
             :: forall id symb repr .
                ( id ~ symb SAT.Var DPRandId
                , Ord id, Pretty id, Show id
                , RPOExtCircuit repr (TermN id)
                , CoRPO repr (TermN id) SAT.Var
                , HasPrecedence SAT.Var id, HasStatus SAT.Var id, HasFiltering SAT.Var id
                ) => ExistSolver symb repr
                  -> [RuleN RandId] -> Property

mkRuleGtProp (ExistSolver ext solve) rules
  = case result of
     Nothing -> label "unsat" True
     Just b  -> property b
 where
   result = solve $ do
                rr <- mkSymbolRules ext rules
                assert [andL [l `termGt` r | l:->r <- rr]]
                return $ evalB (andL [l `termGt` r | l:->r <- rr])


mkRuleEqProp (ExistSolver ext solve) rules
  = case result of
     Nothing -> label "unsat" True
     Just b  -> property b
 where
   result = solve $ do
               rr <- mkSymbolRules ext rules
               assert [andL [l `termEq` r | l:->r <- rr]]
               return $ evalB (andL [l `termEq` r | l:->r <- rr])


smtFFISolverLPO = ExistSolver lpo (unsafePerformIO . smtFFI)
satYicesSimpSolverLPO, satYicesSolverLPO ::
    (Ord id, Pretty id, Show id, Hashable id, AssertCircuit (Shared (TermN (LPOsymbol SAT.Var id)))
    ) => ExistSolver LPOsymbol (Shared (TermN (LPOsymbol SAT.Var id)))
satYicesSimpSolverLPO = ExistSolver lpo (unsafePerformIO . satYicesSimp' 100 (YicesOpts 20 Nothing))
satYicesSolverLPO = ExistSolver lpo (unsafePerformIO . satYices' 100 (YicesOpts 20 Nothing))

smtFFISolverLPOS = ExistSolver lpos (unsafePerformIO . smtFFI)
satYicesSimpSolverLPOS, satYicesSolverLPOS ::
    (Ord id, Pretty id, Show id, Hashable id, AssertCircuit (Shared (TermN (LPOSsymbol SAT.Var id)))
    ) => ExistSolver LPOSsymbol (Shared (TermN (LPOSsymbol SAT.Var id)))
satYicesSimpSolverLPOS = ExistSolver lpos (unsafePerformIO . satYicesSimp' 100 (YicesOpts 20 Nothing))
satYicesSolverLPOS = ExistSolver lpos (unsafePerformIO . satYices' 100 (YicesOpts 20 Nothing))

smtFFISolverMPO = ExistSolver mpo (unsafePerformIO . smtFFI)
satYicesSimpSolverMPO, satYicesSolverMPO ::
    (Ord id, Pretty id, Show id, Hashable id, AssertCircuit (Shared (TermN (MPOsymbol SAT.Var id)))
    ) => ExistSolver MPOsymbol (Shared (TermN (MPOsymbol SAT.Var id)))
satYicesSimpSolverMPO = ExistSolver mpo (unsafePerformIO . satYicesSimp' 100 (YicesOpts 20 Nothing))
satYicesSolverMPO = ExistSolver mpo (unsafePerformIO . satYices' 100 (YicesOpts 20 Nothing))

smtFFISolverRPO = ExistSolver rpo (unsafePerformIO . smtFFI)
satYicesSimpSolverRPO, satYicesSolverRPO ::
    (Ord id, Pretty id, Show id, Hashable id, AssertCircuit (Shared (TermN (RPOsymbol SAT.Var id)))
    ) => ExistSolver RPOsymbol (Shared (TermN (RPOsymbol SAT.Var id)))
satYicesSimpSolverRPO = ExistSolver rpo (unsafePerformIO . satYicesSimp' 100 (YicesOpts 20 Nothing))
satYicesSolverRPO = ExistSolver rpo (unsafePerformIO . satYices' 100 (YicesOpts 20 Nothing))

smtFFISolverRPOS = ExistSolver rpos (unsafePerformIO . smtFFI)
satYicesSimpSolverRPOS, satYicesSolverRPOS ::
    (Ord id, Pretty id, Show id, Hashable id, AssertCircuit (Shared (TermN (RPOSsymbol SAT.Var id)))
    ) => ExistSolver RPOSsymbol (Shared (TermN (RPOSsymbol SAT.Var id)))
satYicesSimpSolverRPOS = ExistSolver rpos (unsafePerformIO . satYicesSimp' 100 (YicesOpts 20 Nothing))
satYicesSolverRPOS = ExistSolver rpos (unsafePerformIO . satYices' 100 (YicesOpts 20 Nothing))


{-
testRuleGtProp ::
                ( id ~ symb SAT.Var DPRandId
                , Ord id, Show id, Hashable id
                , Decode id (SymbolRes DPRandId) SAT.Var
                , RPOExtCircuit (Shared (TermN id)) (TermN id)
                , HasPrecedence SAT.Var id, HasStatus SAT.Var id, HasFiltering SAT.Var id
                ) => ExistSolver symb (Shared (TermN id)) -> [RuleN RandId] -> Maybe (Bool, [SymbolRes DPRandId])
testRuleGtProp (ExistSolver ext solve) rules = solve $ do
               rr <- mkSymbolRules ext rules
               assert [andL [l `termGt` r | l:->r <- rr]]
               return $ do
                 let symbols = toList $ getAllSymbols rr
                 symbolsres <- mapM decode symbols
                 bienv <- ask
                 correct <- evalB (andL [l `termGt` r | l:->r <- rr])
                 () <- Debug.Trace.trace (show symbols) (return ())
                 () <- Debug.Trace.trace (show bienv) (return ())
                 return (correct, symbolsres)

testRuleEqProp ::
                ( id ~ symb SAT.Var DPRandId
                , Ord id, Show id, Hashable id
                , Decode id (SymbolRes DPRandId) SAT.Var
                , RPOExtCircuit (Shared (TermN id)) (TermN id)
                , HasPrecedence SAT.Var id, HasStatus SAT.Var id, HasFiltering SAT.Var id
                ) => ExistSolver symb (Shared (TermN id)) -> [RuleN RandId] -> Maybe (Bool, [SymbolRes DPRandId])
testRuleEqProp (ExistSolver ext solve) rules = solve $ do
               rr <- mkSymbolRules ext rules
               assert [andL [l `termEq` r | l:->r <- rr]]
               return $ do
                 let symbols = toList $ getAllSymbols rr
                 symbolsres <- mapM decode symbols
                 bienv <- ask
                 correct <- evalB (andL [l `termEq` r | l:->r <- rr])
                 () <- Debug.Trace.trace (show symbols) (return ())
                 () <- Debug.Trace.trace (show bienv) (return ())
                 return (correct, symbolsres)
-}


-- Some other stuff
--eqRule, gtRule :: RuleN LDPId -> SAT LDPId Var (EvalM Var (Bool, Bool))
gtRule (l:->r) = assert [l `termGt` r] >> return correct
  where
--   coherent= evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $ (l `termGt` r))
   correct = evalB (l`termGt`r) :: EvalM SAT.Var Bool
eqRule (l:->r) = assert [l `termEq` r] >> return correct
  where
--   coherent= evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $ (l `termEq` r))
   correct = evalB (l`termEq`r)
geRule (l:->r) = assert [l `termGt` r, l `termEq` r] >> return correct
  where
--   coherent= evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $ (l `termEq` r))
   correct = evalB (l`termEq`r)


