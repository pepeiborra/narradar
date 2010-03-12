{-# OPTIONS_GHC -fglasgow-exts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Properties  where

{-
    This file contains portions of code from funsat. (Copyright 2008 Denis Bueno)

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

-}
import Control.Applicative
import Control.Arrow
import qualified Control.Exception as CE ( assert )
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Array.Unboxed
import Data.Bits hiding( xor )
import Data.Foldable (toList)
import Data.List (nub, splitAt)
import Data.Maybe
import Data.Monoid
import Data.Map ( Map)
import Data.Set ( Set )
import Data.Traversable ( traverse )
import Data.NarradarTrie (HasTrie, empty, lookup, insert, (:->:))
import Debug.Trace
import System.IO
import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Text.PrettyPrint.HughesPJClass
import Prelude hiding ( or, and, all, any, elem, minimum
                      , concatMap, sum, concat )
import qualified Prelude

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.NarradarTrie as Trie
import qualified Test.QuickCheck as QC
import qualified Language.CNF.Parse.ParseDIMACS as ParseCNF
import qualified Funsat.Circuit as Funsat

import qualified Narradar.Types as Narradar
import Narradar.Constraints.SAT.Solve
import Narradar.Constraints.SAT.RPOAF ()
import Narradar.Constraints.SAT.RPOAF.Symbols
import Narradar.Constraints.SAT.RPOCircuit as C
import Narradar.Constraints.SAT.RPOCircuit as Circuit
import Narradar.Constraints.SAT.RPOCircuit hiding( Circuit(..), ECircuit(..) )
import Narradar.Constraints.SAT.RPOCircuit
                     ( Circuit(input,true,false)
                     , ECircuit(ite,xor,onlyif)
                     , NatCircuit(eq,lt,nat))
import Narradar.Constraints.SAT.YicesFFICircuit
import Narradar.Types.DPIdentifiers (DPIdentifier(..))
import Narradar.Types.Term

import Funsat.Resolution( ResolutionTrace(..) )
import Funsat.Types hiding (Var, V)
import Funsat.Solver (solve1)
import qualified Funsat.ECircuit as ECircuit
import Language.CNF.Parse.ParseDIMACS as ParseCNF( parseFile, parseByteString)

import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Data.Graph.Inductive
import Data.Graph.Inductive.Graph
import System.Directory
import System.FilePath
import System.IO
import System.Process
import Text.Printf
import Debug.Trace


main :: IO ()
main = defaultMain properties

properties =    properties_circuits
             ++ properties_solvers
             ++ properties_rpo
             ++ properties_various

properties_rpo
          = [ testGroup "LPO Circuits (funsat)" [
                testProperty "equiv rule (1) direct" prop_lporuleEqToCNF_direct,
                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct,
                testProperty "equiv rule (*) direct" prop_lporuleEqToCNF_direct,
                testProperty "decreasing rule (*) direct" prop_lporulesEqToCNF_direct],

--               testGroup "LPO Circuits (Yices)" [
--                 testProperty "equiv rule (1) direct" prop_lporuleEqToCNF_direct_yices,
--                 testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct_yices,
--                 testProperty "equiv rule (*) direct" prop_lporulesEqToCNF_direct_yices,
--                 testProperty "decreasing rule (*) direct" prop_lporulesGtToCNF_direct_yices],

              testGroup "LPO Circuits (Yices SMT FFI)" [
                testProperty "equiv rule (1) direct" prop_lporuleEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct_smtFFI,
                testProperty "equiv rule (*) direct" prop_lporulesEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (*) direct" prop_lporulesGtToCNF_direct_smtFFI],

              testGroup "LPOS Circuits (Yices SMT FFI)" [
                testProperty "equiv rule (1) direct" prop_lposruleEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (1) direct" prop_lposruleGtToCNF_direct_smtFFI,
                testProperty "equiv rule (*) direct" prop_lposrulesEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (*) direct" prop_lposrulesGtToCNF_direct_smtFFI],

--               testGroup "LPOS Circuits (Yices)" [
--                 testProperty "equiv rule (1) direct" prop_lposruleEqToCNF_direct_yices,
--                 testProperty "decreasing rule (1) direct" prop_lposruleGtToCNF_direct_yices,
--                 testProperty "equiv rule (*) direct" prop_lposrulesEqToCNF_direct_yices,
--                 testProperty "decreasing rule (*) direct" prop_lposrulesGtToCNF_direct_yices],

              testGroup "RPO Circuits (Yices SMT FFI)" [
                testProperty "equiv rule (1) direct" prop_rporuleEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (1) direct" prop_rporuleGtToCNF_direct_smtFFI,
                testProperty "equiv rule (*) direct" prop_rporulesEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (*) direct" prop_rporulesGtToCNF_direct_smtFFI],

--               testGroup "RPO Circuits (Yices)" [
--                 testProperty "equiv rule (1) direct" prop_rporuleEqToCNF_direct_yices,
--                 testProperty "decreasing rule (1) direct" prop_rporuleGtToCNF_direct_yices,
--                 testProperty "equiv rule (*) direct" prop_rporulesEqToCNF_direct_yices,
--                 testProperty "decreasing rule (*) direct" prop_rporulesGtToCNF_direct_yices],

              testGroup "RPOS Circuits (Yices SMT FFI)" [
                testProperty "equiv rule (1) direct" prop_rposruleEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (1) direct" prop_rposruleGtToCNF_direct_smtFFI,
                testProperty "equiv rule (*) direct" prop_rposrulesEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (*) direct" prop_rposrulesGtToCNF_direct_smtFFI],

--               testGroup "RPOS Circuits (Yices)" [
--                 testProperty "equiv rule (1) direct" prop_rposruleEqToCNF_direct_yices,
--                 testProperty "decreasing rule (1) direct" prop_rposruleGtToCNF_direct_yices,
--                 testProperty "equiv rule (*) direct" prop_rposrulesEqToCNF_direct_yices,
--                 testProperty "decreasing rule (*) direct" prop_rposrulesGtToCNF_direct_yices],

              testGroup "MPO Circuits (Yices SMT FFI)" [
                testProperty "equiv rule (1) direct" prop_mporuleEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (1) direct" prop_mporuleGtToCNF_direct_smtFFI,
                testProperty "equiv rule (*) direct" prop_mporulesEqToCNF_direct_smtFFI,
                testProperty "decreasing rule (*) direct" prop_mporulesGtToCNF_direct_smtFFI]

--               testGroup "MPO Circuits (Yices)" [
--                 testProperty "equiv rule (1) direct" prop_mporuleEqToCNF_direct_yices,
--                 testProperty "decreasing rule (1) direct" prop_mporuleGtToCNF_direct_yices,
--                 testProperty "equiv rule (*) direct" prop_mporulesEqToCNF_direct_yices,
--                 testProperty "decreasing rule (*) direct" prop_mporulesGtToCNF_direct_yices]
             ]

properties_solvers = [
              testGroup "Solvers-ecircuits" [
--                testProperty "simplify ext" prop_solvers_ecircuits_simp,
                testProperty "simplify" prop_solvers_ecircuits_simp,
                testProperty "direct" prop_solvers_ecircuits_direct
                            ],
              testGroup "Solvers-natcircuits" [
--                testProperty "simplify nats" prop_solvers_natcircuits_simp,
                testProperty "simplify" prop_solvers_natcircuits_simp,
                testProperty "direct" prop_solvers_natcircuits_direct
                             ],
              testGroup "Solvers-onecircuits" [
                testProperty "simplify" prop_solvers_onecircuits_simp,
--                testProperty "direct" prop_solvers_onecircuits_direct,
                testProperty "direct" prop_solvers_onecircuits_direct
                             ],
              testGroup "Solvers-lpocircuits" [
--                testProperty "simplify" prop_solvers_lpocircuits_simp,
--                testProperty "simplify all" prop_solvers_lpocircuits_simp,
                testProperty "direct" prop_solvers_lpocircuits_direct
                             ]]
properties_circuits = [
              testGroup "Extended Circuits (Funsat)" [
                testProperty "direct" prop_ecircuitToCnf,
                testProperty "simplify(1)" prop_ecircuitToCnf_simp1
--                testProperty "simplify" prop_ecircuitToCnf_simp
                            ],
              testGroup "Circuits with naturals (funsat)" [
--                testProperty "simplify nats: " prop_natcircuitToCnf_simp,
--                testProperty "simplify nats(1): "  prop_natcircuitToCnf_simp1,
                testProperty "direct"  prop_natcircuitToCnf_direct],
              testGroup "Circuits with one predicates (funsat)" [
--                testProperty "simplify : " prop_onecircuitToCnf_simp,
--                testProperty "simplify (1): "  prop_onecircuitToCnf_simp1,
                testProperty "direct"  prop_onecircuitToCnf_direct],
              testGroup "LPO Circuits (funsat)" [
--                testProperty "simplify one and nats: " prop_lpocircuitToCnf_simp,
--                testProperty "simplify one: "  prop_lpocircuitToCnf_simp1,
                testProperty "direct"  prop_lpocircuitToCnf_direct],
              testGroup "LPO+status Circuits (funsat)" [
--                testProperty "simplify one and nats: " prop_lposcircuitToCnf_simp,
--                testProperty "simplify one: "  prop_lposcircuitToCnf_simp1,
                testProperty "direct"  prop_lposcircuitToCnf_direct],
              -- testGroup "MPO Circuits (funsat)" [
              --   testProperty "simplify one and nats: " prop_mpocircuitToCnf_simp,
              --   testProperty "simplify one: "  prop_mpocircuitToCnf_simp1,
              --   testProperty "direct"  prop_mpocircuitToCnf_direct],
              testGroup "Extended Circuits (Yices)" [
                testProperty "simplify 1" prop_ecircuitToCnf_simp1_yices,
--                testProperty "simplify" prop_ecircuitToCnf_simp_yices,
                testProperty "direct" prop_ecircuitToCnf_direct_yices],
              testGroup "Circuits with naturals (Yices)" [
--                testProperty "simplify nats: " prop_natcircuitToCnf_simp_yices,
                testProperty "simplify nats(1): "  prop_natcircuitToCnf_simp1_yices,
                testProperty "direct"  prop_natcircuitToCnf_direct_yices],
              testGroup "Circuits with one predicates (Yices)" [
--                testProperty "simplify : " prop_onecircuitToCnf_simp_yices,
--                testProperty "simplify (1): "  prop_onecircuitToCnf_simp1_yices,
                testProperty "direct"  prop_onecircuitToCnf_direct_yices],
              testGroup "LPO Circuits (Yices)" [
--                testProperty "simplify all: " prop_lpocircuitToCnf_simp_yices,
--                testProperty "simplify one: "  prop_lpocircuitToCnf_simp1_yices,
                testProperty "direct"  prop_lpocircuitToCnf_direct_yices],
              testGroup "LPO+Status Circuits (Yices)" [
--                testProperty "simplify all: " prop_lposcircuitToCnf_simp_yices,
--                testProperty "simplify one: "  prop_lposcircuitToCnf_simp1_yices,
                testProperty "direct"  prop_lposcircuitToCnf_direct_yices
                            ],

              testGroup "LPO Circuits (SMTFFI)" [
                testProperty "direct"  prop_lpocircuitToCnf_direct_smtffi],
              testGroup "LPO+Status Circuits (SMTFFI)" [
                testProperty "direct"  prop_lposcircuitToCnf_direct_smtffi
                            ]
              ]

properties_various = [
              testGroup "Testing the tests" [
                testProperty "Enum NVar" (\(Positive i) -> fromEnum (toEnum i :: NVar) == i)
--                ,testProperty "Enum NVar(2)" (\(i::NVar) -> toEnum (fromEnum i) == i)
                            ]
             ]

check :: Testable a => a -> IO ()
check = quickCheckWith stdArgs { maxSuccess = 5000 }

-- -------------------------------
-- ** Circuits and CNF conversion
-- -------------------------------
type SizedGen a = Int -> Gen a

prop_ecircuitToCnf        = mkFunsatDirectProp (sizedECircuit :: SizedGen (Tree Id Var))
--prop_ecircuitToCnf_simp   = mkFunsatSimpProp   (sizedECircuit :: SizedGen (Tree Id Var))
prop_ecircuitToCnf_simp1  = mkFunsatSimp1Prop  (sizedECircuit :: SizedGen (Tree Id Var))

prop_natcircuitToCnf_direct = mkFunsatDirectProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
--prop_natcircuitToCnf_simp   = mkFunsatSimpProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
prop_natcircuitToCnf_simp1  = mkFunsatSimp1Prop (sizedNatCircuit :: SizedGen (Tree Id NVar))

prop_onecircuitToCnf_direct = mkFunsatDirectProp (sizedOneCircuit :: SizedGen (Tree Id Var))
--prop_onecircuitToCnf_simp   = mkFunsatSimpProp (sizedOneCircuit :: SizedGen (Tree Id Var))
prop_onecircuitToCnf_simp1  = mkFunsatSimp1Prop (sizedOneCircuit :: SizedGen (Tree Id Var))

prop_lpocircuitToCnf_direct   = mkFunsatDirectRPOProp (liftM fst . sizedLPOCircuit)
--prop_lpocircuitToCnf_simp     = mkFunsatSimpRPOProp   sizedLPOCircuit
prop_lpocircuitToCnf_simp1    = mkFunsatSimp1RPOProp  sizedLPOCircuit

prop_lposcircuitToCnf_direct   = mkFunsatDirectRPOProp (liftM fst . sizedLPOsCircuit)
--prop_lposcircuitToCnf_simp     = mkFunsatSimpRPOProp   sizedLPOsCircuit
prop_lposcircuitToCnf_simp1    = mkFunsatSimp1RPOProp  sizedLPOsCircuit

prop_mpocircuitToCnf_direct   = mkFunsatDirectRPOProp (liftM fst . sizedMPOCircuit)
--prop_mpocircuitToCnf_simp     = mkFunsatSimpRPOProp   sizedMPOCircuit
prop_mpocircuitToCnf_simp1    = mkFunsatSimp1RPOProp  sizedMPOCircuit

prop_ecircuitToCnf_direct_yices = mkYicesDirectProp (sizedECircuit :: SizedGen (Tree Id Var))
--prop_ecircuitToCnf_simp_yices   = mkYicesSimpProp   (sizedECircuit :: SizedGen (Tree Id Var))
prop_ecircuitToCnf_simp1_yices  = mkYicesSimp1Prop  (sizedECircuit :: SizedGen (Tree Id Var))

prop_natcircuitToCnf_direct_yices = mkYicesDirectProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
--prop_natcircuitToCnf_simp_yices   = mkYicesSimpProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
prop_natcircuitToCnf_simp1_yices  = mkYicesSimp1Prop (sizedNatCircuit :: SizedGen (Tree Id NVar))

prop_onecircuitToCnf_direct_yices = mkYicesDirectProp (sizedOneCircuit :: SizedGen (Tree Id Var))
--prop_onecircuitToCnf_simp_yices   = mkYicesSimpProp (sizedOneCircuit :: SizedGen (Tree Id Var))
prop_onecircuitToCnf_simp1_yices  = mkYicesSimp1Prop (sizedOneCircuit :: SizedGen (Tree Id Var))

prop_lpocircuitToCnf_direct_yices = mkYicesDirectRPOProp (liftM fst . sizedLPOCircuit)
--prop_lpocircuitToCnf_simp_yices   = mkYicesSimpRPOProp   sizedLPOCircuit
prop_lpocircuitToCnf_simp1_yices  = mkYicesSimp1RPOProp  sizedLPOCircuit

prop_lposcircuitToCnf_direct_yices  = mkYicesDirectRPOProp (liftM fst . sizedLPOsCircuit)

prop_lpocircuitToCnf_direct_smtffi  = mkSMTDirectRPOProp (liftM fst . sizedLPOCircuit)
prop_lposcircuitToCnf_direct_smtffi = mkSMTDirectRPOProp (liftM fst . sizedLPOsCircuit)


trivial pred = classify pred "Trivial"

instance OneCircuit ECircuit.Shared

mkFunsatSimp1Prop :: forall id v.
                    ( Ord v, HasTrie v, Show v, Bounded v, Enum v, DefaultValue v (Either Int Bool)
                    , Ord id, HasTrie id, Show id
                    ) => SizedGen (Tree id v) -> Property
mkFunsatSimp1Prop gen = forAll (sized gen) $ \c ->
    let (pblm@(ECircuitProblem{ eproblemCnf = cnf }), natbits)
           = toCNF' [toEnum 10000..]
           . (runShared :: Shared id v -> FrozenShared id v)
           . castCircuit $ c
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = reconstructNatsFromBits (Trie.toList natbits) $ projectECircuitSolution solution pblm
                      benv' = benv `mappend` defaultValues (toList c)
                  in   label "Sat"
                     . trivial (Map.null benv)
                     . fromRight . runEval benv' . castCircuit . simplifyTree $ c

         Unsat{} -> label "Unsat (unverified)" True

mkFunsatDirectProp :: forall id v.
                    ( Ord v, HasTrie v, Show v, Bounded v, Enum v, DefaultValue v (Either Int Bool)
                    , Ord id, HasTrie id, Show id
                    ) => SizedGen (Tree id v) -> Property
mkFunsatDirectProp gen = forAll (sized gen) $ \c ->
    let pblm@(RPOCircuitProblem{ rpoProblemCnf = cnf })
           = toCNF
           . (runShared :: Shared id v -> FrozenShared id v)
           . castCircuit $ c
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                      benv' = benv `mappend` defaultValues (toList c)
                  in   label "Sat"
                     . trivial (Map.null benv)
                     . fromRight . runEval benv' . castCircuit . simplifyTree $ c

         Unsat{} -> label "Unsat (unverified)" True

{-
mkFunsatSimpRPOProp :: forall v id.
                       (Ord v, HasTrie v, Show v, Bounded v, Enum v
                       ,Ord id, Pretty id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ,RPOExtCircuit (Shared id) id
                       ) => SizedGen (Tree id v) -> Property
-}
mkFunsatSimp1RPOProp gen = forAll (sized gen) mkFunsatSimp1RPOProp'
mkFunsatSimp1RPOProp' (c, pool)  =
    let (pblm@(ECircuitProblem{ eproblemCnf = cnf }), natbits)
           = toCNF' pool
           . runShared
--           . (castRPOCircuit :: Tree id v -> Shared id v)
           . (castRPOCircuit :: (Ord v, HasTrie v, Show v, RPOExtCircuit (Shared id) id, Ord id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id) => Tree id v -> Shared id v)
           $ c
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv  = reconstructNatsFromBits (Trie.toList natbits) $ projectECircuitSolution solution pblm
                      benv' = benv `mappend` defaultValues (toList c)
                  in   label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castRPOCircuit $ simplifyTree c)

         Unsat{} -> label "Unsat (unverified)" True

mkFunsatDirectRPOProp gen = forAll (sized gen) mkFunsatDirectRPOProp'
mkFunsatDirectRPOProp' c  =
    let pblm@(RPOCircuitProblem{ rpoProblemCnf = cnf })
           = toCNF
           . runShared
--           . (castRPOCircuit :: Tree id v -> Shared id v)
           . (castRPOCircuit :: (Ord v, HasTrie v, Show v, RPOExtCircuit (Shared id) id, Ord id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id) => Tree id v -> Shared id v)
           $ c
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                      benv' = benv `mappend` defaultValues (toList c)
                  in   label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castRPOCircuit $ simplifyTree c)

         Unsat{} -> label "Unsat (unverified)" True


mkYicesDirectProp :: forall id v.
                     (Ord v, HasTrie v, Show v, Bounded v, Enum v
                     ,Ord id, Show id, HasTrie id
                     ) => SizedGen (Tree id v) -> Property
mkYicesDirectProp gen = forAll (sized gen) $ \c ->
    let correct = unsafePerformIO $
                  satYices defaultYicesOpts
                    ((assert [castCircuit c]  :: SAT id v ()) >>
                     return (evalB (castCircuit $ simplifyTree c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimp1Prop :: forall id v.
                    (Ord v, HasTrie v, Show v, Bounded v, Enum v
                    ,Ord id, Show id, HasTrie id
                    ) => SizedGen (Tree id v) -> Property
mkYicesSimp1Prop gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  satYicesSimp' [toEnum 1000..] defaultYicesOpts
                    ((assert [castCircuit c]  :: SAT id v ()) >>
                     return (evalB (castCircuit $ simplifyTree c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x


mkYicesDirectRPOProp :: forall id v. ( Ord v, HasTrie v, Show v, Bounded v, Enum v
                                     , Ord id, Show id, HasTrie id
                                     , HasPrecedence v id, HasFiltering v id, HasStatus v id
                                     , RPOExtCircuit (Shared id) id
                                     ) => SizedGen (Tree id v) -> Property
mkYicesDirectRPOProp gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  satYices defaultYicesOpts
                    (assert [castRPOCircuit c]  >>
                     return (evalB (castRPOCircuit $ simplifyTree c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimp1RPOProp :: forall id v.
                       (Ord v, HasTrie v, Show v, Bounded v, Enum v
                       ,Ord id, HasTrie id, Show id
                       ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ,RPOExtCircuit (Shared id) id
                       ) => SizedGen (Tree id v,[v]) -> Property
mkYicesSimp1RPOProp gen = forAll (sized gen) $ \(c :: Tree id v, pool) ->
    let correct = unsafePerformIO $
                  satYicesSimp' pool defaultYicesOpts
                    (assert [castCircuit c :: Shared id v] >>
                     return (evalB (castRPOCircuit $ simplifyTree c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x


mkSMTDirectRPOProp :: forall id v. ( v ~ Var, Ord v, HasTrie v, Show v, Bounded v, Enum v
                                   , Ord id, Show id, HasTrie id, Pretty id
                                   , HasPrecedence v id, HasFiltering v id, HasStatus v id
                                   , RPOExtCircuit (YicesSource id) id
                                   ) => SizedGen (Tree id v) -> Property
mkSMTDirectRPOProp gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  smtFFI
                  (assert [castRPOCircuit c]  >>
                     return (evalB (castRPOCircuit $ simplifyTree c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

-- --------------------
-- Solver sanity checks
-- --------------------
{-
prop_solvers_ecircuits_simp = forAll (sized sizedECircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF [V 1000..] $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 withYices' defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
-}
prop_solvers_ecircuits_simp = forAll (sized sizedECircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      (pblm, natbits)  = toCNF' [V 200..] $ runShared shrd
      (sol,_,_) = solve1 $ eproblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices' [V 200..] defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_ecircuits_direct = forAll (sized sizedECircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF$ runShared shrd
      (sol,_,_) = solve1 $ rpoProblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices [V 200 ..] defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
{-
prop_solvers_natcircuits_simp = forAll (sized sizedNatCircuit) $ \(c :: Tree Id NVar) ->
  let shrd  = castCircuit c :: Shared Id NVar
      pblm  = toCNF' [VB 1000..] $ runShared shrd
      (sol,_,_) = solve1 $ eproblemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 withYices' defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
-}
prop_solvers_natcircuits_simp = forAll (sized sizedNatCircuit) $ \(c :: Tree Id NVar) ->
  let shrd  = castCircuit c :: Shared Id NVar
      (pblm,_)  = toCNF' [VB 200..] $ runShared shrd
      (sol,_,_) = solve1 $ eproblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices' [VB 200..] defaultYicesOpts (assert [shrd] :: SAT Id NVar ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_natcircuits_direct = forAll (sized sizedNatCircuit) $ \(c :: Tree Id NVar) ->
  let shrd  = castCircuit c :: Shared Id NVar
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ rpoProblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices [VB 200 ..] defaultYicesOpts (assert [shrd] :: SAT Id NVar ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
{-
prop_solvers_onecircuits_simp = forAll (sized sizedOneCircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF [V 10000..] $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 withYices' defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
-}
prop_solvers_onecircuits_simp = forAll (sized sizedOneCircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      (pblm,_)  = toCNF' [V 2000..] $ runShared shrd
      (sol,_,_) = solve1 $ eproblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices' [V 2000 ..] defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_onecircuits_direct = forAll (sized sizedOneCircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ rpoProblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices [V 2000 ..] defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
{-
prop_solvers_lpocircuits_simp = forAll (sized sizedLPOCircuit) $ \(c :: Tree LDPId Var) ->
  let shrd  = castRPOCircuit c :: Shared LDPId Var
      pblm  = toCNF [V 1000..]  $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 withYices' defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol
-}
prop_solvers_lpocircuits_simp = forAll (sized sizedLPOCircuit) $ \(c :: Tree LDPId Var, pool) ->
  let shrd  = castRPOCircuit c :: Shared LDPId Var
      (pblm,_) = toCNF' pool $ runShared shrd
      (sol,_,_) = solve1 $ eproblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices' [V 2000 ..] defaultYicesOpts (assert [shrd] :: SAT LDPId Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_lpocircuits_direct = forAll (sized sizedLPOCircuit) $ \(c :: Tree LDPId Var, pool) ->
  let shrd  = castRPOCircuit c :: Shared LDPId Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ rpoProblemCnf pblm
      yicesSol = unsafePerformIO $
                 withYices [V 2000 ..] defaultYicesOpts (assert [shrd] :: SAT LDPId Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

isUnsat Sat{} = False
isUnsat Unsat{} = True


withYices pool0 yo (SAT m) = do
  let (val, St _ circuit weighted) = runState m (St pool0 true [])
  let circuitProb = toCNF(runShared circuit)
  solveYices yo (rpoProblemCnf circuitProb) weighted val


withYices' pool0 yo (SAT m) = do
  let (val, St pool circuit weighted) = runState m (St pool0 true [])
      (circuitProb,_) = toCNF' pool (runShared circuit)
  solveYices yo (eproblemCnf circuitProb) weighted val

-- -----------------------
-- RPO order comparisons
-- -----------------------

prop_lporuleGtToCNF_direct :: RuleN Id -> Property
prop_lporuleGtToCNF_direct = mkRuleGtProp lpo (ExistSolver solveFunDirect) . (:[])

prop_lporuleGtToCNF_direct_yices :: RuleN Id -> Property
prop_lporuleGtToCNF_direct_yices = mkRuleGtProp lpo (ExistSolver satYicesSolver) . (:[])

prop_lporuleGtToCNF_direct_smtFFI :: RuleN Id -> Property
prop_lporuleGtToCNF_direct_smtFFI = mkRuleGtProp lpo (ExistSolver smtFFISolver) . (:[])

prop_lporuleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_lporuleGtToCNF_simp1_yices = mkRuleGtProp lpo (ExistSolver satYicesSimpSolver) . (:[])

prop_lporuleGtToCNF_simp_yices :: RuleN Id -> Property
prop_lporuleGtToCNF_simp_yices = mkRuleGtProp lpo (ExistSolver satYicesSimpSolver) . (:[])

prop_lporuleEqToCNF_direct :: RuleN Id -> Property
prop_lporuleEqToCNF_direct = mkRuleEqProp lpo (ExistSolver solveFunDirect) . (:[])

prop_lporuleEqToCNF_direct_yices :: RuleN Id -> Property
prop_lporuleEqToCNF_direct_yices = mkRuleEqProp lpo (ExistSolver satYicesSolver) . (:[])

prop_lporuleEqToCNF_direct_smtFFI :: RuleN Id -> Property
prop_lporuleEqToCNF_direct_smtFFI = mkRuleEqProp lpo (ExistSolver(unsafePerformIO . smtFFI)) . (:[])

prop_lporuleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_lporuleEqToCNF_simp1_yices = mkRuleEqProp lpo (ExistSolver satYicesSimpSolver) . (:[])

prop_lporuleEqToCNF_simp_yices :: RuleN Id -> Property
prop_lporuleEqToCNF_simp_yices = mkRuleEqProp lpo (ExistSolver satYicesSimpSolver) . (:[])


prop_lporulesGtToCNF_direct :: [RuleN Id] -> Property
prop_lporulesGtToCNF_direct = mkRuleGtProp lpo (ExistSolver solveFunDirect)

prop_lporulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_lporulesGtToCNF_direct_yices = mkRuleGtProp lpo (ExistSolver satYicesSolver)

prop_lporulesGtToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_lporulesGtToCNF_direct_smtFFI = mkRuleGtProp lpo (ExistSolver(unsafePerformIO . smtFFI))

prop_lporulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_lporulesGtToCNF_simp1_yices = mkRuleGtProp lpo (ExistSolver satYicesSimpSolver)

prop_lporulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_lporulesGtToCNF_simp_yices = mkRuleGtProp lpo (ExistSolver satYicesSimpSolver)

prop_lporulesEqToCNF_direct :: [RuleN Id] -> Property
prop_lporulesEqToCNF_direct = mkRuleEqProp lpo (ExistSolver solveFunDirect)

prop_lporulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_lporulesEqToCNF_direct_yices = mkRuleEqProp lpo (ExistSolver satYicesSolver)

prop_lporulesEqToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_lporulesEqToCNF_direct_smtFFI = mkRuleEqProp lpo (ExistSolver(unsafePerformIO . smtFFI))

prop_lporulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_lporulesEqToCNF_simp1_yices = mkRuleEqProp lpo (ExistSolver satYicesSimpSolver)

prop_lporulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_lporulesEqToCNF_simp_yices = mkRuleEqProp lpo (ExistSolver satYicesSimpSolver)


prop_lposruleGtToCNF_direct :: RuleN Id -> Property
prop_lposruleGtToCNF_direct = mkRuleGtProp lpos (ExistSolver solveFunDirect) . (:[])

prop_lposruleGtToCNF_direct_yices :: RuleN Id -> Property
prop_lposruleGtToCNF_direct_yices = mkRuleGtProp lpos (ExistSolver satYicesSolver) . (:[])

prop_lposruleGtToCNF_direct_smtFFI :: RuleN Id -> Property
prop_lposruleGtToCNF_direct_smtFFI = mkRuleGtProp lpos (ExistSolver(unsafePerformIO . smtFFI)) . (:[])

prop_lposruleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_lposruleGtToCNF_simp1_yices = mkRuleGtProp lpos (ExistSolver satYicesSimpSolver) . (:[])

prop_lposruleGtToCNF_simp_yices :: RuleN Id -> Property
prop_lposruleGtToCNF_simp_yices = mkRuleGtProp lpos (ExistSolver satYicesSimpSolver) . (:[])

prop_lposruleEqToCNF_direct :: RuleN Id -> Property
prop_lposruleEqToCNF_direct = mkRuleEqProp lpos (ExistSolver solveFunDirect) . (:[])

prop_lposruleEqToCNF_direct_yices :: RuleN Id -> Property
prop_lposruleEqToCNF_direct_yices = mkRuleEqProp lpos (ExistSolver satYicesSolver) . (:[])

prop_lposruleEqToCNF_direct_smtFFI :: RuleN Id -> Property
prop_lposruleEqToCNF_direct_smtFFI = mkRuleEqProp lpos (ExistSolver(unsafePerformIO . smtFFI)) . (:[])

prop_lposruleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_lposruleEqToCNF_simp1_yices = mkRuleEqProp lpos (ExistSolver satYicesSimpSolver) . (:[])

prop_lposruleEqToCNF_simp_yices :: RuleN Id -> Property
prop_lposruleEqToCNF_simp_yices = mkRuleEqProp lpos (ExistSolver satYicesSimpSolver) . (:[])


prop_lposrulesGtToCNF_direct :: [RuleN Id] -> Property
prop_lposrulesGtToCNF_direct = mkRuleGtProp lpos (ExistSolver solveFunDirect)

prop_lposrulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_lposrulesGtToCNF_direct_yices = mkRuleGtProp lpos (ExistSolver satYicesSolver)

prop_lposrulesGtToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_lposrulesGtToCNF_direct_smtFFI = mkRuleGtProp lpos (ExistSolver(unsafePerformIO . smtFFI))

prop_lposrulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_lposrulesGtToCNF_simp1_yices = mkRuleGtProp lpos (ExistSolver satYicesSimpSolver)

prop_lposrulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_lposrulesGtToCNF_simp_yices = mkRuleGtProp lpos (ExistSolver satYicesSimpSolver)

prop_lposrulesEqToCNF_direct :: [RuleN Id] -> Property
prop_lposrulesEqToCNF_direct = mkRuleEqProp lpos (ExistSolver solveFunDirect)

prop_lposrulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_lposrulesEqToCNF_direct_yices = mkRuleEqProp lpos (ExistSolver satYicesSolver)

prop_lposrulesEqToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_lposrulesEqToCNF_direct_smtFFI = mkRuleEqProp lpos (ExistSolver(unsafePerformIO . smtFFI))

prop_lposrulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_lposrulesEqToCNF_simp1_yices = mkRuleEqProp lpos (ExistSolver satYicesSimpSolver)

prop_lposrulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_lposrulesEqToCNF_simp_yices = mkRuleEqProp lpos (ExistSolver satYicesSimpSolver)


prop_mporuleGtToCNF_direct :: RuleN Id -> Property
prop_mporuleGtToCNF_direct = mkRuleGtProp mpo (ExistSolver solveFunDirect) . (:[])

prop_mporuleGtToCNF_direct_yices :: RuleN Id -> Property
prop_mporuleGtToCNF_direct_yices = mkRuleGtProp mpo (ExistSolver satYicesSolver) . (:[])

prop_mporuleGtToCNF_direct_smtFFI :: RuleN Id -> Property
prop_mporuleGtToCNF_direct_smtFFI = mkRuleGtProp mpo (ExistSolver(unsafePerformIO . smtFFI)) . (:[])

prop_mporuleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_mporuleGtToCNF_simp1_yices = mkRuleGtProp mpo (ExistSolver satYicesSimpSolver) . (:[])

prop_mporuleGtToCNF_simp_yices :: RuleN Id -> Property
prop_mporuleGtToCNF_simp_yices = mkRuleGtProp mpo (ExistSolver satYicesSimpSolver) . (:[])

prop_mporuleEqToCNF_simp :: RuleN Id -> Property
prop_mporuleEqToCNF_simp = mkRuleEqProp mpo (ExistSolver solveFun) . (:[])

prop_mporuleEqToCNF_direct :: RuleN Id -> Property
prop_mporuleEqToCNF_direct = mkRuleEqProp mpo (ExistSolver solveFunDirect) . (:[])

prop_mporuleEqToCNF_direct_yices :: RuleN Id -> Property
prop_mporuleEqToCNF_direct_yices = mkRuleEqProp mpo (ExistSolver satYicesSolver) . (:[])

prop_mporuleEqToCNF_direct_smtFFI :: RuleN Id -> Property
prop_mporuleEqToCNF_direct_smtFFI = mkRuleEqProp mpo (ExistSolver(unsafePerformIO .smtFFI)) . (:[])

prop_mporuleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_mporuleEqToCNF_simp1_yices = mkRuleEqProp mpo (ExistSolver satYicesSimpSolver) . (:[])

prop_mporuleEqToCNF_simp_yices :: RuleN Id -> Property
prop_mporuleEqToCNF_simp_yices = mkRuleEqProp mpo (ExistSolver satYicesSimpSolver) . (:[])


prop_mporulesGtToCNF_direct :: [RuleN Id] -> Property
prop_mporulesGtToCNF_direct = mkRuleGtProp mpo (ExistSolver solveFunDirect)

prop_mporulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_mporulesGtToCNF_direct_yices = mkRuleGtProp mpo (ExistSolver satYicesSolver)

prop_mporulesGtToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_mporulesGtToCNF_direct_smtFFI = mkRuleGtProp mpo (ExistSolver(unsafePerformIO . smtFFI))

prop_mporulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_mporulesGtToCNF_simp1_yices = mkRuleGtProp mpo (ExistSolver satYicesSimpSolver)

prop_mporulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_mporulesGtToCNF_simp_yices = mkRuleGtProp mpo (ExistSolver satYicesSimpSolver)

prop_mporulesEqToCNF_direct :: [RuleN Id] -> Property
prop_mporulesEqToCNF_direct = mkRuleEqProp mpo (ExistSolver solveFunDirect)

prop_mporulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_mporulesEqToCNF_direct_yices = mkRuleEqProp mpo (ExistSolver satYicesSolver)

prop_mporulesEqToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_mporulesEqToCNF_direct_smtFFI = mkRuleEqProp mpo (ExistSolver(unsafePerformIO . smtFFI))

prop_mporulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_mporulesEqToCNF_simp1_yices = mkRuleEqProp mpo (ExistSolver satYicesSimpSolver)

prop_mporulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_mporulesEqToCNF_simp_yices = mkRuleEqProp mpo (ExistSolver (unsafePerformIO . satYicesSimp' [toEnum 100..] (YicesOpts 20 Nothing)))

---

prop_rporuleGtToCNF_direct :: RuleN Id -> Property
prop_rporuleGtToCNF_direct = mkRuleGtProp rpo (ExistSolver solveFunDirect) . (:[])

prop_rporuleGtToCNF_direct_yices :: RuleN Id -> Property
prop_rporuleGtToCNF_direct_yices = mkRuleGtProp rpo (ExistSolver satYicesSolver) . (:[])

prop_rporuleGtToCNF_direct_smtFFI :: RuleN Id -> Property
prop_rporuleGtToCNF_direct_smtFFI = mkRuleGtProp rpo (ExistSolver(unsafePerformIO . smtFFI)) . (:[])

prop_rporuleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_rporuleGtToCNF_simp1_yices = mkRuleGtProp rpo (ExistSolver satYicesSimpSolver) . (:[])

prop_rporuleGtToCNF_simp_yices :: RuleN Id -> Property
prop_rporuleGtToCNF_simp_yices = mkRuleGtProp rpo (ExistSolver satYicesSimpSolver) . (:[])

prop_rporuleEqToCNF_simp :: RuleN Id -> Property
prop_rporuleEqToCNF_simp = mkRuleEqProp rpo (ExistSolver solveFun) . (:[])

prop_rporuleEqToCNF_direct :: RuleN Id -> Property
prop_rporuleEqToCNF_direct = mkRuleEqProp rpo (ExistSolver solveFunDirect) . (:[])

prop_rporuleEqToCNF_direct_yices :: RuleN Id -> Property
prop_rporuleEqToCNF_direct_yices = mkRuleEqProp rpo (ExistSolver satYicesSolver) . (:[])

prop_rporuleEqToCNF_direct_smtFFI :: RuleN Id -> Property
prop_rporuleEqToCNF_direct_smtFFI = mkRuleEqProp rpo (ExistSolver(unsafePerformIO .smtFFI)) . (:[])

prop_rporuleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_rporuleEqToCNF_simp1_yices = mkRuleEqProp rpo (ExistSolver satYicesSimpSolver) . (:[])

prop_rporuleEqToCNF_simp_yices :: RuleN Id -> Property
prop_rporuleEqToCNF_simp_yices = mkRuleEqProp rpo (ExistSolver satYicesSimpSolver) . (:[])


prop_rporulesGtToCNF_direct :: [RuleN Id] -> Property
prop_rporulesGtToCNF_direct = mkRuleGtProp rpo (ExistSolver solveFunDirect)

prop_rporulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_rporulesGtToCNF_direct_yices = mkRuleGtProp rpo (ExistSolver satYicesSolver)

prop_rporulesGtToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_rporulesGtToCNF_direct_smtFFI = mkRuleGtProp rpo (ExistSolver(unsafePerformIO . smtFFI))

prop_rporulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_rporulesGtToCNF_simp1_yices = mkRuleGtProp rpo (ExistSolver satYicesSimpSolver)

prop_rporulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_rporulesGtToCNF_simp_yices = mkRuleGtProp rpo (ExistSolver satYicesSimpSolver)

prop_rporulesEqToCNF_direct :: [RuleN Id] -> Property
prop_rporulesEqToCNF_direct = mkRuleEqProp rpo (ExistSolver solveFunDirect)

prop_rporulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_rporulesEqToCNF_direct_yices = mkRuleEqProp rpo (ExistSolver satYicesSolver)

prop_rporulesEqToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_rporulesEqToCNF_direct_smtFFI = mkRuleEqProp rpo (ExistSolver(unsafePerformIO . smtFFI))

prop_rporulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_rporulesEqToCNF_simp1_yices = mkRuleEqProp rpo (ExistSolver satYicesSimpSolver)

prop_rporulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_rporulesEqToCNF_simp_yices = mkRuleEqProp rpo (ExistSolver satYicesSimpSolver)


prop_rposruleGtToCNF_direct :: RuleN Id -> Property
prop_rposruleGtToCNF_direct = mkRuleGtProp rpos (ExistSolver solveFunDirect) . (:[])

prop_rposruleGtToCNF_direct_yices :: RuleN Id -> Property
prop_rposruleGtToCNF_direct_yices = mkRuleGtProp rpos (ExistSolver satYicesSolver) . (:[])

prop_rposruleGtToCNF_direct_smtFFI :: RuleN Id -> Property
prop_rposruleGtToCNF_direct_smtFFI = mkRuleGtProp rpos (ExistSolver smtFFISolver) . (:[])

prop_rposruleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_rposruleGtToCNF_simp1_yices = mkRuleGtProp rpos (ExistSolver satYicesSimpSolver) . (:[])

prop_rposruleGtToCNF_simp_yices :: RuleN Id -> Property
prop_rposruleGtToCNF_simp_yices = mkRuleGtProp rpos (ExistSolver satYicesSimpSolver) . (:[])

prop_rposruleEqToCNF_simp :: RuleN Id -> Property
prop_rposruleEqToCNF_simp = mkRuleEqProp rpos (ExistSolver solveFun) . (:[])

prop_rposruleEqToCNF_direct :: RuleN Id -> Property
prop_rposruleEqToCNF_direct = mkRuleEqProp rpos (ExistSolver solveFunDirect) . (:[])

prop_rposruleEqToCNF_direct_yices :: RuleN Id -> Property
prop_rposruleEqToCNF_direct_yices = mkRuleEqProp rpos (ExistSolver satYicesSolver) . (:[])

prop_rposruleEqToCNF_direct_smtFFI :: RuleN Id -> Property
prop_rposruleEqToCNF_direct_smtFFI = mkRuleEqProp rpos (ExistSolver smtFFISolver) . (:[])

prop_rposruleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_rposruleEqToCNF_simp1_yices = mkRuleEqProp rpos (ExistSolver satYicesSimpSolver) . (:[])

prop_rposruleEqToCNF_simp_yices :: RuleN Id -> Property
prop_rposruleEqToCNF_simp_yices = mkRuleEqProp rpos (ExistSolver satYicesSimpSolver) . (:[])


prop_rposrulesGtToCNF_direct :: [RuleN Id] -> Property
prop_rposrulesGtToCNF_direct = mkRuleGtProp rpos (ExistSolver solveFunDirect)

prop_rposrulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_rposrulesGtToCNF_direct_yices = mkRuleGtProp rpos (ExistSolver satYicesSolver)

prop_rposrulesGtToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_rposrulesGtToCNF_direct_smtFFI = mkRuleGtProp rpos (ExistSolver smtFFISolver)

prop_rposrulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_rposrulesGtToCNF_simp1_yices = mkRuleGtProp rpos (ExistSolver satYicesSimpSolver)

prop_rposrulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_rposrulesGtToCNF_simp_yices = mkRuleGtProp rpos (ExistSolver satYicesSimpSolver)

prop_rposrulesEqToCNF_direct :: [RuleN Id] -> Property
prop_rposrulesEqToCNF_direct = mkRuleEqProp rpos (ExistSolver solveFunDirect)

prop_rposrulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_rposrulesEqToCNF_direct_yices = mkRuleEqProp rpos (ExistSolver satYicesSolver)

prop_rposrulesEqToCNF_direct_smtFFI :: [RuleN Id] -> Property
prop_rposrulesEqToCNF_direct_smtFFI = mkRuleEqProp rpos (ExistSolver smtFFISolver)

prop_rposrulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_rposrulesEqToCNF_simp1_yices = mkRuleEqProp rpos (ExistSolver satYicesSimpSolver)

prop_rposrulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_rposrulesEqToCNF_simp_yices = mkRuleEqProp rpos (ExistSolver satYicesSimpSolver)

-- ---------------------------------------
-- helpers for interactive testing in GHCi
-- ---------------------------------------
{-
testRulePropYicesDirect ext rules k = satYices (YicesOpts 20 Nothing)
                                                  (mkSymbolRules ext rules >>= detailedOutputFor k)
testRulePropYicesSimp1  ext rules k = satYicesSimp (YicesOpts 20 Nothing)
                                                  (mkSymbolRules ext rules >>= detailedOutputFor k)
testRulePropYicesSimp   ext rules k = solveYicesSimp (YicesOpts 20 Nothing)
                                                  (mkSymbolRules ext rules >>= detailedOutputFor k)

testRulePropFun ext rules k = solveFun (mkSymbolRules ext rules >>= detailedOutputFor k)
--testRuleProp' :: [RuleN id] ->
-}
detailedOutputFor k symbol_rules = do
    correct_m <- k symbol_rules
    return $ do
      benv    <- ask
      (sound,correct) <- liftM ((Prelude.and *** Prelude.and) . unzip) $ sequence correct_m
      let symbols = toList $ getAllSymbols symbol_rules
      symbols' <- mapM decode symbols
      return (sound, correct, benv, symbols, symbols' :: [RDPId])

testRulePropDirect' ::
              (sid ~ symb Var DPId, HasTrie sid, Ord sid, Show sid, Pretty sid)
              => SymbolFactory symb
              -> [RuleN Id]
              -> ( [RuleN sid] -> SAT sid Var (EvalM Var a) )
              -> IO (Maybe (BIEnv Var   -- Var mapping
                           ,[RuleN sid]    -- SAT symbol rules
                           ,a)) -- (correctness) for every rule

testRulePropDirect' ext rules k = do
    let SAT satComp = do
          symbols <- mkSymbolRules ext rules
--          (coherent, correct) <- liftM ((Prelude.and *** Prelude.and) . unzip) $ mapM k symbols
          res <- k symbols
          return (res, symbols)

        ((res, symbols), St _ circuit _weighted) = runState satComp (St [V 1 ..] true [])

        frozen = runShared circuit
        pblm = toCNF $ frozen
        (solution,_,_) = solve1 $ rpoProblemCnf pblm

    let frozenGr = isGraph $ shareGraph' frozen
        isGraph :: Gr a b -> Gr a b
        isGraph = id

    putStrLn "The frozen simplified circuit:"
    print frozen
--    putStrLn "The represented formula:"
--    print (printTree 0 $ castCircuit frozen)

--    putStrLn "The symbols"
--    print (getAllSymbols rules)

    tmp <- getTemporaryDirectory
    (tmpFile,hTmpFile) <- openTempFile tmp "shareGraph.dot"
    hPutStrLn hTmpFile (graphviz' frozenGr)
    hClose hTmpFile
    system (printf "dot -Tpdf %s -O && open %s" tmpFile (tmpFile <.> "pdf"))
--    system ("open " ++ tmpFile)

    case solution of
         Sat{} -> let bienv = projectRPOCircuitSolution solution pblm
                  in return $ Just (bienv, symbols, runEvalM bienv res)

         Unsat{} -> return Nothing

testRulePropSimp' ::
              (sid ~ symb Var DPId, HasTrie sid, Ord sid, Show sid, Pretty sid)
              => SymbolFactory symb
              -> [RuleN Id]
              -> ( [RuleN sid] -> SAT sid Var (EvalM Var a) )
              -> IO (Maybe (BIEnv Var   -- Var mapping
                           ,[RuleN sid]    -- SAT symbol rules
                           ,a)) -- (correctness) for every rule
testRulePropSimp' ext rules k = do
    let SAT satComp = do
          symbols <- mkSymbolRules ext rules
--          (coherent, correct) <- liftM ((Prelude.and *** Prelude.and) . unzip) $ mapM k symbols
          res <- k symbols
          return (res, symbols)
        ((res, symbols), St pool circuit _weighted) = runState satComp (St [V 1 ..] true [])
        frozen = runShared circuit
        (pblm, natbits) = toCNF' pool frozen
        (solution,_,_) = solve1 $ eproblemCnf pblm

    let frozenGr = isGraph $ shareGraph' frozen
        isGraph :: forall a b. Gr a b -> Gr a b
        isGraph = id

    putStrLn "The frozen simplified circuit:"
    print frozen
--    putStrLn "The represented formula:"
--    print (printTree 0 $ castCircuit frozen)

--    putStrLn "The symbols"
--    print (getAllSymbols rules)

    tmp <- getTemporaryDirectory
    (tmpFile,hTmpFile) <- openTempFile tmp "shareGraph.dot"
    hPutStrLn hTmpFile (graphviz' frozenGr)
    hClose hTmpFile
    system (printf "dot -Tpdf %s -O && open %s" tmpFile (tmpFile <.> "pdf"))
--    system ("open " ++ tmpFile)

    case solution of
         Sat{} -> let benv = reconstructNatsFromBits (Trie.toList natbits) $ projectECircuitSolution solution pblm
                  in return $ Just (benv, symbols, runEvalM benv res)

         Unsat{} -> return Nothing

--eqRule, gtRule :: RuleN LDPId -> SAT LDPId Var (EvalM Var (Bool, Bool))
gtRule (l:->r) = assert [l `termGt` r] >> return correct
  where
--   coherent= evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $ (l `termGt` r))
   correct = evalB (l`termGt`r) :: EvalM Var Bool
eqRule (l:->r) = assert [l `termEq` r] >> return correct
  where
--   coherent= evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $ (l `termEq` r))
   correct = evalB (l`termEq`r)
geRule (l:->r) = assert [l `termGt` r, l `termEq` r] >> return correct
  where
--   coherent= evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $ (l `termEq` r))
   correct = evalB (l`termEq`r)

data ExistSolver symb = forall repr m .
                        ( RPOCircuit repr (symb Var DPId)
                        , Decode (symb Var DPId) (SymbolRes DPId) Var
                        , Show (symb Var DPId)
                        , MonadSAT repr Var m) =>
                        ExistSolver (forall a. m (EvalM Var a) -> Maybe a)


smtFFISolver   = (unsafePerformIO . smtFFI)
satYicesSimpSolver = (unsafePerformIO . satYicesSimp' [toEnum 100..] (YicesOpts 20 Nothing))
satYicesSolver = (unsafePerformIO . satYices' [toEnum 100..] (YicesOpts 20 Nothing))

mkRuleGtProp, mkRuleEqProp
             :: (id ~ symb Var DPId, Ord id, RPOExtCircuit (Shared id) id
                ,HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                ) => SymbolFactory symb -> ExistSolver symb -> [RuleN Id] -> Property
mkRuleGtProp ext (ExistSolver solve) rules
  = case solve result of
     Nothing -> label "unsat" True
     Just b  -> property b
 where
   result = do
                rr <- mkSymbolRules ext rules
                assert [andL [l `termGt` r | l:->r <- rr]]
                return $ evalB (andL [l `termGt` r | l:->r <- rr])

--mkRuleEqProp :: (id ~ symb Var DPId, Ord id, Show id, RPOExtCircuit (Shared id) id
--                ,HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
--                ) => SymbolFactory symb -> (SAT id Var (EvalM Var Bool) -> Maybe Bool) -> [RuleN Id] -> Property
--mkRuleEqProp :: SymbolFactory symb ->
mkRuleEqProp ext (ExistSolver solve) rules
  = case result of
     Nothing -> label "unsat" True
     Just b  -> property b
 where
   result = solve $ do
               rr <- mkSymbolRules ext rules
               assert [andL [l `termEq` r | l:->r <- rr]]
               return $ evalB (andL [l `termEq` r | l:->r <- rr])

mkSymbolRules :: (MonadSAT repr Var m, id ~ symb Var DPId) => SymbolFactory symb -> [RuleN Id] -> m [RuleN id]
--mkSymbolRules :: [RuleN Id] -> SAT id Var [RuleN LDPId]
mkSymbolRules ext rr = do
     let symbols = toList $ getAllSymbols rr
     symbols'   <- mapM (mkSATSymbol ext) symbols
     let convert = fromJust . (`Map.lookup` dict)
         dict    = Map.fromList (zip symbols symbols')
         rr_s    = (fmap.fmap) (mapTermSymbols convert) rr
     return rr_s

testRuleGtProp ::
                (id ~ symb Var DPId, Ord id, RPOExtCircuit (Shared id) id
                ,HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                ) => SymbolFactory symb -> ExistSolver symb -> [RuleN Id] -> Maybe (Bool, [SymbolRes DPId])
testRuleGtProp ext (ExistSolver solve) rules = solve $ do
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
                (id ~ symb Var DPId, Ord id, RPOExtCircuit (Shared id) id
                ,HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                ) => SymbolFactory symb -> ExistSolver symb -> [RuleN Id] -> Maybe (Bool, [SymbolRes DPId])
testRuleEqProp ext (ExistSolver solve) rules = solve $ do
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

{-
test_circuitToCnfBS :: [Eval NVar] -> Circuit.Tree Id NVar -> IO ()
test_circuitToCnfBS vars treeCircuit = do
    let frozen :: FrozenShared Id NVar
        frozen = runShared . castCircuit $ treeCircuit
        pblm = unsafePerformIO . toCNFBS $ frozen
        dimacs = asDimacs . eproblemCnf $ pblm
        (solution,_,_) = (solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" ) dimacs

    print frozen
    putStrLn ""
--    print (removeHashCount $ removeNats frozen)
    putStrLn ""
    print (eproblemCodeMap pblm)
    print (eproblemBitMap pblm)
    BS.putStrLn dimacs

    print solution

    case solution of
         Sat{} -> let benv = projectECircuitSolution solution pblm
                  in do print benv
                        print $ map (runEval benv) vars
                        putStrLn ""
                        print $ fromRight $ runEval benv (castCircuit treeCircuit)

         Unsat{} -> putStrLn "Unsat"
-}

test_circuitToCnf :: forall id. (HasTrie id, Ord id, Show id) => [Eval NVar] -> Tree id NVar -> IO ()
test_circuitToCnf vars treeCircuit =
    let pblm@(RPOCircuitProblem{ rpoProblemCnf = cnf }) =
            toCNF $ runShared (castCircuit treeCircuit :: Shared id NVar)
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                  in do print $ map (runEval benv) vars
                        putStrLn ""
                        print $ fromRight $ runEval benv (castCircuit treeCircuit)

         Unsat{} -> putStrLn "Unsat"
{-
test_circuitToCnfRPO :: [Eval NVar] -> Circuit.Tree id NVar -> IO ()
test_circuitToCnfRPO vars treeCircuit = do
    let frozen :: FrozenShared Id NVar
        frozen = runShared . castCircuit $ treeCircuit
        pblm = unsafePerformIO . toCNFRPO $ frozen
        dimacs = asDimacs . rpoProblemCnf $ pblm
        (solution,_,_) = (solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" ) dimacs

    print frozen
    putStrLn ""
--    print (removeHashCount $ removeNats frozen)
    putStrLn "\nCode Map:"
    print (rpoProblemCodeMap pblm)
    putStrLn "\n Bit Map:"
    print (rpoProblemBitMap pblm)
    BS.putStrLn dimacs

    print solution

    case solution of
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                  in do print benv
                        print $ map (runEval benv) vars
                        putStrLn ""
                        print $ fromRight $ runEval benv (castCircuit treeCircuit)

         Unsat{} -> putStrLn "Unsat"

-- TXor (TNot (TIff (TLeaf 1v) (TLeaf 1v))) (TXor TFalse TFalse)


test_ecircuitToCnf :: [Eval Var] -> ECircuit.Tree Var -> IO ()
test_ecircuitToCnf vars treeCircuit =
    let pblm@(CircuitProblem{ problemCnf = cnf }) =
            toCNF . runShared . castCircuit $ treeCircuit
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectCircuitSolution solution pblm
                  in do print $ map (runEval benv) vars
                        putStrLn ""
                        print $ fromRight $ runEval benv (castCircuit treeCircuit)

         Unsat{} -> putStrLn "Unsat"
-}
fromRight (Right x) = x

-- -------------------------------------
-- default values for unbound variables
-- -------------------------------------
class DefaultValue v b where defaultValue :: v -> b
instance DefaultValue Var (Either Int Bool) where
  defaultValue _ = Right False
instance DefaultValue NVar (Either Int Bool) where
  defaultValue VN{} = Left 0
  defaultValue VB{} = Right False


defaultValues vv = Map.fromList [ (v, defaultValue v) | v <- vv]
-- -----------------
-- Generators
-- -----------
sizedCircuit :: Circuit c => Int -> Gen (c Var)
sizedCircuit 0 = return . input . V $ 1
sizedCircuit n =
    oneof [ return true
          , return false
          , (return . input . V) n
          , liftM2 C.and subcircuit2 subcircuit2
          , liftM2 C.or  subcircuit2 subcircuit2
          , liftM C.not subcircuit1
          ]
  where subcircuit2 = sizedCircuit (n `div` 2)
        subcircuit1 = sizedCircuit (n - 1)

-- | Generator for a circuit containing at most `n' nodes, involving only the
-- literals 1 .. n.
sizedECircuit :: ECircuit c => Int -> Gen (c Var)
sizedECircuit 0 = return . input . V $ 1
sizedECircuit n =
    oneof [ return true
          , return false
          , (return . input . V) n
          , liftM2 C.and subcircuit2 subcircuit2
          , liftM2 C.or  subcircuit2 subcircuit2
          , liftM C.not subcircuit1
          , liftM3 ite subcircuit3 subcircuit3 subcircuit3
          , liftM2 onlyif subcircuit2 subcircuit2
          , liftM2 C.iff subcircuit2 subcircuit2
          , liftM2 xor subcircuit2 subcircuit2
          ]
  where subcircuit3 = sizedECircuit (n `div` 3)
        subcircuit2 = sizedECircuit (n `div` 2)
        subcircuit1 = sizedECircuit (n - 1)

-- | Generator for a circuit containing at most `n' nodes, involving only the
-- literals 1 .. n.
sizedOneCircuit :: (ECircuit c, OneCircuit c) => Int -> Gen (c Var)
sizedOneCircuit 0 = return . input . V $ 1
sizedOneCircuit n =
    oneof [ return true
          , return false
          , (return . input . V) n
          , liftM2 C.and subcircuit2 subcircuit2
          , liftM2 C.or  subcircuit2 subcircuit2
          , liftM C.not subcircuit1
          , return $ one (map (input.V) [0..n])
          ]
  where subcircuit2 = sizedOneCircuit (n `div` 2)
        subcircuit1 = sizedOneCircuit (n - 1)

data NVar = VN Int | VB Int deriving (Eq, Ord)

vb i     = input $ VB i

instance Show NVar where
  show (VN i) = "vn" ++ show i
  show (VB i) = "vb" ++ show i

instance Read NVar where
  readsPrec p ('v':'n':rest) = [(VN i, rest) | (i,rest) <- readsPrec 0 rest]
  readsPrec p ('v':'b':rest) = [(VB i, rest) | (i,rest) <- readsPrec 0 rest]
  readsPrec _ _ = []

instance Bounded NVar where minBound = VN 0; maxBound = VB maxBound
instance Enum NVar where
--  fromEnum (VN i) = i * 2
--  fromEnum (VB i) = (i * 2) + 1
--  toEnum i = (if odd i then VB else VN) (i `div` 2)
  toEnum i = VB i
  fromEnum (VB i) = i

instance Arbitrary NVar where
  arbitrary = do {con <- elements [VB,VN]; (con . abs) `liftM` arbitrary}
instance Decode NVar Bool NVar where decode v@VB{} = evalB (input v)
--instance Decode [NVar] Integer NVar where decode vv = evalN (ECircuit.nat vv)
instance HasTrie NVar where
  data NVar :->: x = NVarTrie !(Int :->: x) !(Int :->: x)
  empty = NVarTrie Trie.empty Trie.empty
  lookup (VN v) (NVarTrie nt _) = Trie.lookup v nt
  lookup (VB v) (NVarTrie _ bt) = Trie.lookup v bt
  insert (VN x) v (NVarTrie nt bt) = NVarTrie (Trie.insert x v nt) bt
  insert (VB x) v (NVarTrie nt bt) = NVarTrie nt (Trie.insert x v nt)
  toList (NVarTrie nt bt) = map (first VN) (Trie.toList nt) ++
                            map (first VB) (Trie.toList bt)


sizedNatCircuit :: (Functor c, ECircuit c, OneCircuit c, NatCircuit c) => Int -> Gen (c NVar)
sizedNatCircuit 0 = return . vb $ 1
sizedNatCircuit n =
    oneof [ return true
          , return false
          , (return . vb) n
          , liftM2 C.and subcircuit2 subcircuit2'
          , liftM2 C.or  subcircuit2 subcircuit2'
          , liftM C.not subcircuit1
          , return $ eq (mkNat n) (mkNat (n-1))
          , return $ lt (mkNat n) (mkNat (n-1))
          ]
  where subcircuit2  = sizedNatCircuit (n `div` 2)
        subcircuit1  = sizedNatCircuit (n - 1)
        subcircuit2' = (fmap.fmap) convert $ sizedCircuit (n `div` 2)
        convert (V i)= VB i
        mkNat = ECircuit.nat . VN

sizedOneNatECircuit :: (Functor c, ECircuit c, OneCircuit c, NatCircuit c) => Int -> Gen (c NVar)
sizedOneNatECircuit 0 = return . input . VB $ 1
sizedOneNatECircuit n =
    oneof [ return true
          , return false
          , (return . input . VB) n
          , liftM2 C.and subcircuit2 subcircuit2'
          , liftM2 C.or  subcircuit2 subcircuit2'
          , liftM C.not subcircuit1
          , liftM3 ite subcircuit3' subcircuit3 subcircuit3'
          , liftM2 onlyif subcircuit2 subcircuit2'
          , liftM2 C.iff subcircuit2 subcircuit2'
          , liftM2 xor subcircuit2 subcircuit2'
          , return $ eq (mkNat n) (mkNat (n-1))
          , return $ lt (mkNat n) (mkNat (n-1))
          , return $ one (map (input.VB) [0..n])
          ]
  where subcircuit3  = sizedOneNatECircuit (n `div` 3)
        subcircuit2  = sizedOneNatECircuit (n `div` 2)
        subcircuit1  = sizedOneNatECircuit (n - 1)
        subcircuit2' = (fmap.fmap) vb $ sizedOneCircuit (n `div` 2)
        subcircuit3' = (fmap.fmap) vb $ sizedOneCircuit (n `div` 3)
        mkNat        = ECircuit.nat .  VN
        vb (V i)     = VB i


sizedLPOCircuit :: forall c. (ECircuit c, OneCircuit c, RPOCircuit c LDPId) => Int -> Gen (c Var, [Var])
sizedLPOCircuit = sizedxPOCircuit undefined -- :: LPOsymbol Var DPId)

sizedMPOCircuit :: forall c. (ECircuit c, OneCircuit c, RPOCircuit c (MPOsymbol Var DPId)) => Int -> Gen (c Var, [Var])
sizedMPOCircuit = sizedxPOCircuit undefined

sizedLPOsCircuit :: forall c. (ECircuit c, OneCircuit c, RPOCircuit c (LPOSsymbol Var DPId)) => Int -> Gen (c Var, [Var])
sizedLPOsCircuit = sizedxPOCircuit undefined -- :: LPOSsymbol Var DPId)

type Proxy a = a

sizedxPOCircuit :: forall c (lpoid :: * -> * -> *) id.
                   (HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                   ,id ~ lpoid Var (DPIdentifier Id)
                   ,Ord id, HasTrie id
                   ,ECircuit c, OneCircuit c, NatCircuit c, RPOCircuit c id
                   ,Arbitrary (SAT' Id lpoid Var (RuleN id))
                   ) => Proxy id -> Int -> Gen (c Var, [Var])
sizedxPOCircuit _ size = do
  c <- go size
  let (circuit, St pool constraints _) = runSAT' c
  return (circuit `and` removeExist (runShared constraints), pool)
 where
  go :: Int -> Gen (SAT' Id lpoid Var (c Var))
  go 0 = return . return . input . V $ 1
  go n =
    oneof [ return (return true)
          , return (return false)
          , (return . return . input . V) n
          , (liftM2.liftM2) C.and subcircuit2 subcircuit2
          , (liftM2.liftM2) C.or  subcircuit2 subcircuit2
          , (liftM.liftM)   C.not subcircuit1
          , termConstraint
          ]
     where
        subcircuit2    = go (n `div` 2)
        subcircuit1    = go (n - 1)
        termConstraint = do
          rule <- arbitrary
          cmp  <- elements [termGt, termEq]
          return $ liftM (\(l:->r) -> cmp l r) rule


instance OneCircuit ECircuit.Tree

instance Arbitrary (ECircuit.Tree Var) where
    arbitrary = sized sizedECircuit
    shrink    = shrinkETree
instance Arbitrary (Tree id Var) where
    arbitrary = sized sizedCircuit
    shrink    = shrinkTree
instance Arbitrary (Tree id NVar) where
    arbitrary = sized sizedOneNatECircuit
    shrink    = shrinkTree

shrinkTree (TIff a b) = [a,b] ++ tail [TIff a' b' | a' <- a:shrink a
                                                  , b' <- b:shrink b]
shrinkTree (TOnlyIf a b) = [a,b] ++ tail [TOnlyIf a' b'
                                              | a' <- a:shrink a
                                              , b' <- b:shrink b]
shrinkTree (TAnd a b) = [a, b] ++ tail[TAnd a' b'
                                           | a' <- a:shrink a
                                           , b' <- b:shrink b]
shrinkTree (TOr a b)  = [a,b] ++ tail[TOr a' b'
                                          | a' <- a:shrink a
                                          , b' <- b:shrink b]
shrinkTree (TXor a b) = [a,b] ++ tail[TXor a' b' | a' <- a:shrink a
                                                 , b' <- b:shrink b]
shrinkTree (TNot a)   = [a] ++ tail[TNot a' | a' <- shrink a]
shrinkTree (TIte a b c) = [a,b,c] ++ tail[TIte a b c
                                              | a' <- a:shrink a
                                              , b' <- b:shrink b
                                              , c' <- c:shrink c]
shrinkTree (TEq uu vv) = [TEq uu' vv' | uu' <- shrink uu
                                      , vv' <- shrink vv]
shrinkTree (TLt uu vv) = [TLt uu' vv' | uu' <- shrink uu
                                      , vv' <- shrink vv]
shrinkTree (TOne (_:vv)) = [TOne vv]
shrinkTree t = []

shrinkETree (ECircuit.TIff a b) = [a,b] ++ tail [ECircuit.TIff a' b' | a' <- a:shrink a
                                                  , b' <- b:shrink b]
shrinkETree (ECircuit.TOnlyIf a b) = [a,b] ++ tail [ECircuit.TOnlyIf a' b'
                                              | a' <- a:shrink a
                                              , b' <- b:shrink b]
shrinkETree (ECircuit.TAnd a b) = [a, b] ++ tail[ECircuit.TAnd a' b'
                                           | a' <- a:shrink a
                                           , b' <- b:shrink b]
shrinkETree (ECircuit.TOr a b)  = [a,b] ++ tail[ECircuit.TOr a' b'
                                          | a' <- a:shrink a
                                          , b' <- b:shrink b]
shrinkETree (ECircuit.TXor a b) = [a,b] ++ tail[ECircuit.TXor a' b' | a' <- a:shrink a
                                                 , b' <- b:shrink b]
shrinkETree (ECircuit.TNot a)   = [a] ++ tail[ECircuit.TNot a' | a' <- shrink a]
shrinkETree (ECircuit.TIte a b c) = [a,b,c] ++ tail[ECircuit.TIte a b c
                                              | a' <- a:shrink a
                                              , b' <- b:shrink b
                                              , c' <- c:shrink c]
shrinkETree (ECircuit.TEq uu vv) = [ECircuit.TEq uu' vv' | uu' <- shrink uu
                                      , vv' <- shrink vv]
shrinkETree (ECircuit.TLt uu vv) = [ECircuit.TLt uu' vv' | uu' <- shrink uu
                                      , vv' <- shrink vv]
shrinkETree t = []

data Id = F | F2 | G | G2 | S | Z deriving (Eq, Ord, Show)
instance Pretty Id where pPrint = text . show
instance HasTrie Id where
  data Id :->: x = IdTrie (Maybe x) (Maybe x) (Maybe x) (Maybe x) (Maybe x) (Maybe x)
  empty = IdTrie Nothing Nothing Nothing Nothing Nothing Nothing
  lookup F  (IdTrie f _  _ _  _ _) = f
  lookup F2 (IdTrie _ f2 _ _  _ _) = f2
  lookup G  (IdTrie _ _  g _  _ _) = g
  lookup G2 (IdTrie _ _ _  g2 _ _) = g2
  lookup S  (IdTrie _ _ _ _   s _) = s
  lookup Z  (IdTrie _ _ _ _ _   z) = z
  insert F  v (IdTrie f f2 g g2 s z) = IdTrie (Just v) f2 g g2 s z
  insert F2 v (IdTrie f f2 g g2 s z) = IdTrie f (Just v) g g2 s z
  insert G  v (IdTrie f f2 g g2 s z) = IdTrie f f2 (Just v) g2 s z
  insert G2 v (IdTrie f f2 g g2 s z) = IdTrie f f2 g (Just v) s z
  insert S v  (IdTrie f f2 g g2 s z) = IdTrie f f2 g g2 (Just v) z
  insert Z v  (IdTrie f f2 g g2 s z) = IdTrie f f2 g g2 s (Just v)
  toList (IdTrie f f2 g g2 s z) = catMaybes [(,) F  `fmap` f
                                            ,(,) F2 `fmap` f2
                                            ,(,) G  `fmap` g
                                            ,(,) G2 `fmap` g2
                                            ,(,) S  `fmap` s
                                            ,(,) Z  `fmap` z]


-- Generating Terms

type DPId  = DPIdentifier Id
type LPOId = LPOsymbol NVar Id
type LDPId = LPOsymbol Var DPId
type RDPId = SymbolRes DPId

instance Arbitrary Id
 where
  arbitrary = elements [F,G,F2,G2,S,Z]
  shrink F2 = [F]
  shrink G2 = [G]
  shrink _  = []

--instance Arbitrary DPId where arbitrary = elements [IdDP F, IdDP G, IdFunction S, IdFunction Z]

class IsDefined id where isDefined :: id -> Bool

instance IsDefined Id where
 isDefined F = True
 isDefined G = True
 isDefined F2 = True
 isDefined _ = False

instance HasArity Id where
  getIdArity F  = 1
  getIdArity G  = 1
  getIdArity F2 = 2
  getIdArity G2 = 2
  getIdArity S  = 1
  getIdArity Z  = 0

instance IsDefined a => IsDefined (RPOSsymbol v a) where isDefined = isDefined . theSymbol
deriving instance IsDefined a => IsDefined (LPOsymbol v a)
deriving instance IsDefined a => IsDefined (MPOsymbol v a)
deriving instance IsDefined a => IsDefined (RPOsymbol v a)
deriving instance IsDefined a => IsDefined (LPOSsymbol v a)

mkSATSymbol mk F  = mk (IdFunction F, 1, True)
mkSATSymbol mk G  = mk (IdFunction G, 1, True)
mkSATSymbol mk F2 = mk (IdFunction F2, 2, True)
mkSATSymbol mk G2 = mk (IdFunction G2, 2, True)
mkSATSymbol mk S  = mk (IdFunction S, 1, False)
mkSATSymbol mk Z  = mk (IdFunction Z, 0,False)


mkSymbol F = createSymbol 0 0 F 1
mkSymbol G = createSymbol 5 2 G 1
mkSymbol S = createSymbol 10 4 S 1
mkSymbol Z = createSymbol 15 6 Z 0
mkSymbol F2 = createSymbol 20 8 F2 2
mkSymbol G2 = createSymbol 30 10 G2 2

createSymbol ::  Show id => Int -> Int -> id -> Int -> LPOsymbol NVar id
createSymbol b0 n0 id 2
  = LPO $ Symbol
              { theSymbol    = id
              , encodePrec   = encodeNatural prec
              , encodeUsable = vb 1
              , encodeAFlist = vb 2
              , encodeAFpos  = [vb 3, vb 4]
              , encodePerm   = [[vb 5, vb 6], [vb 7, vb 8]]
              , encodeUseMset= vb 9
              , decodeSymbol = mkSymbolDecoder id prec (vb 1) (vb 2) [vb 3, vb 4] [[vb 5, vb 6], [vb 7, vb 8]] (vb 9)
              }

 where
  vb i = VB (b0 + i)
  vn i = VN (n0 + i)
  prec = Natural (vn 1)

createSymbol b0 n0 id 1
  = LPO $ Symbol
              { theSymbol    = id
              , encodePrec   = encodeNatural prec
              , encodeUsable = vb 1
              , encodeAFlist = vb 2
              , encodeAFpos  = [vb 3]
              , encodePerm   = [[vb 4]]
              , encodeUseMset= vb 5
              , decodeSymbol = mkSymbolDecoder id prec (vb 1) (vb 2) [vb 3] [[vb 4]] (vb 5)
              }

 where
  vb i = VB (b0 + i)
  vn i = VN (n0 + i)
  prec = Natural (vn 1)

createSymbol b0 n0 id 0
  = LPO $ Symbol
              { theSymbol = id
              , encodePrec = encodeNatural prec
              , encodeUsable = vb 1
              , encodeAFlist = vb 2
              , encodeAFpos  = []
              , encodePerm   = []
              , encodeUseMset = vb 3
              , decodeSymbol = mkSymbolDecoder id prec (vb 1) (vb 2) [] [] (vb 3)}
 where
  vb i = VB (b0 + i)
  vn i = VN (n0 + i)
  prec = Natural (vn 1)

sizedTerm, sizedDefTerm :: (HasArity id, IsDefined id, Arbitrary id) => Int -> Gen (TermN id)
sizedTerm size = oneof [return $ Narradar.var 0
                       ,return $ Narradar.var 1
                       ,do
  id <- arbitrary
  let ar = getIdArity id
  tt <- replicateM ar (sizedTerm (size `div` (1 + ar)))
  return (term id tt)]

sizedDefTerm size = do
  id <- arbitrary `suchThat` isDefined
  let ar = getIdArity id
  tt <- replicateM ar (sizedTerm (size `div` (1 + ar)))
  return (term id tt)

instance (HasArity id, IsDefined id, Arbitrary id) => Arbitrary (TermN id)
  where
   arbitrary = sized sizedTerm
   shrink (Impure (Term id tt)) = [Impure (Term id' tt') | id' <- shrink id ++ [id]
                                                         , tt' <- take (getIdArity id) $ mapM shrink tt]
   shrink t = []

instance (HasArity id, IsDefined id, Arbitrary id) => Arbitrary (RuleN id)
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      return ( lhs :-> rhs )
   shrink (l :-> r) = init [ l' :-> r' | l' <- shrink l ++ [l], r' <- shrink r ++ [r]]

instance Arbitrary (SAT' Id LPOsymbol Var (RuleN LDPId))
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      let rule  = lhs :-> rhs
          symbs = toList $ getAllSymbols rule
      return $ traverse (mapTermSymbolsM (mkSATSymbol' lpo)) rule

instance Arbitrary (SAT' Id MPOsymbol Var (RuleN (MPOsymbol Var DPId)))
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      let rule  = lhs :-> rhs
          symbs = toList $ getAllSymbols rule
      return $ traverse (mapTermSymbolsM (mkSATSymbol' mpo)) rule

instance Arbitrary (SAT' Id LPOSsymbol Var (RuleN (LPOSsymbol Var DPId)))
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      let rule  = lhs :-> rhs
          symbs = toList $ getAllSymbols rule
      return $ traverse (mapTermSymbolsM (mkSATSymbol' lpos)) rule


type SAT' id lpoid v = StateT (Map id (lpoid v (DPIdentifier id))  )
                              (SAT    (lpoid v (DPIdentifier id)) v)

runSAT' = (`runState` st0{pool=[V 1000..]}) . unSAT . (`evalStateT` Map.empty)

--mkSATSymbol' :: Id -> SAT' Id Var LDPId
mkSATSymbol' mk s = do
  dict <- get
  case Map.lookup s dict of
    Just sat -> return sat
    _        -> do
      s' <- lift $ mkSATSymbol mk s
      modify (Map.insert s s')
      return s'

-- --------
-- Helpers
-- --------

-- | Convert parsed CNF to internal representation.
asCNF :: ParseCNF.CNF -> CNF
asCNF (ParseCNF.CNF v c is) =
    CNF {numVars = v
        ,numClauses = c
        ,clauses = map (map fromIntegral . elems) $ is}
