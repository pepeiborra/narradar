{-# OPTIONS_GHC -fglasgow-exts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PackageImports #-}

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
import Narradar.Types.DPIdentifiers (DPIdentifier(..))
import Narradar.Types.Term

import Funsat.Resolution( ResolutionTrace(..) )
import Funsat.Types hiding (Var, V)
import Funsat.Solver (solve1)
import Funsat.ECircuit (projectCircuitSolution)
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
          = [ testGroup "RPO Circuits (funsat)" [
                testProperty "decreasing rule (1) simplify all" prop_lporuleGtToCNF_simp,
--                testProperty "decreasing rule (1) simplify ones" prop_lporuleGtToCNF_simp1,
--                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct],
                testProperty "equiv rule (1) simplify all" prop_lporuleEqToCNF_simp,
--                ,testProperty "decreasing rule (1) simplify ones" prop_lporuleGtToCNF_simp1,
--                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct],
                testProperty "decreasing rule (*) simplify all" prop_lporulesGtToCNF_simp,
--                testProperty "decreasing rule (1) simplify ones" prop_lporuleGtToCNF_simp1,
--                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct],
                testProperty "equiv rule (*) simplify all" prop_lporulesEqToCNF_simp
--                ,testProperty "decreasing rule (1) simplify ones" prop_lporuleGtToCNF_simp1,
--                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct],
              ],
              testGroup "LPO Circuits (Yices)" [
                testProperty "equiv rule (1) simplify all" prop_lporuleEqToCNF_simp_yices,
                testProperty "equiv rule (1) simplify ones" prop_lporuleEqToCNF_simp1_yices,
                testProperty "equiv rule (1) direct" prop_lporuleEqToCNF_direct_yices,
                testProperty "decreasing rule (1) simplify all" prop_lporuleGtToCNF_simp_yices,
                testProperty "decreasing rule (1) simplify ones" prop_lporuleGtToCNF_simp1_yices,
                testProperty "decreasing rule (1) direct" prop_lporuleGtToCNF_direct_yices,
                testProperty "equiv rule (*) simplify all" prop_lporulesEqToCNF_simp_yices,
                testProperty "equiv rule (*) simplify ones" prop_lporulesEqToCNF_simp1_yices,
                testProperty "equiv rule (*) direct" prop_lporulesEqToCNF_direct_yices,
                testProperty "decreasing rule (*) simplify all" prop_lporulesGtToCNF_simp_yices,
                testProperty "decreasing rule (*) simplify ones" prop_lporulesGtToCNF_simp1_yices,
                testProperty "decreasing rule (*) direct" prop_lporulesGtToCNF_direct_yices],

              testGroup "MPO Circuits (Yices)" [
                testProperty "equiv rule (1) simplify all" prop_mporuleEqToCNF_simp_yices,
                testProperty "equiv rule (1) simplify ones" prop_mporuleEqToCNF_simp1_yices,
                testProperty "equiv rule (1) direct" prop_mporuleEqToCNF_direct_yices,
                testProperty "decreasing rule (1) simplify all" prop_mporuleGtToCNF_simp_yices,
                testProperty "decreasing rule (1) simplify ones" prop_mporuleGtToCNF_simp1_yices,
                testProperty "decreasing rule (1) direct" prop_mporuleGtToCNF_direct_yices,
                testProperty "equiv rule (*) simplify all" prop_mporulesEqToCNF_simp_yices,
                testProperty "equiv rule (*) simplify ones" prop_mporulesEqToCNF_simp1_yices,
                testProperty "equiv rule (*) direct" prop_mporulesEqToCNF_direct_yices,
                testProperty "decreasing rule (*) simplify all" prop_mporulesGtToCNF_simp_yices,
                testProperty "decreasing rule (*) simplify ones" prop_mporulesGtToCNF_simp1_yices,
                testProperty "decreasing rule (*) direct" prop_mporulesGtToCNF_direct_yices]
            ]

properties_solvers = [
              testGroup "Solvers-ecircuits" [
                testProperty "simplify ext" prop_solvers_ecircuits_simp,
                testProperty "direct" prop_solvers_ecircuits_direct,
                testProperty "direct" prop_solvers_ecircuits_directRPO
                            ],
              testGroup "Solvers-natcircuits" [
                testProperty "simplify nats" prop_solvers_natcircuits_simp,
                testProperty "direct" prop_solvers_natcircuits_direct,
                testProperty "direct" prop_solvers_natcircuits_directRPO
                             ],
              testGroup "Solvers-onecircuits" [
                testProperty "simplify ones" prop_solvers_onecircuits_simp,
                testProperty "direct" prop_solvers_onecircuits_direct,
                testProperty "direct" prop_solvers_onecircuits_directRPO
                             ],
              testGroup "Solvers-lpocircuits" [
                testProperty "simplify ones" prop_solvers_lpocircuits_simp1,
                testProperty "simplify all" prop_solvers_lpocircuits_simp,
                testProperty "direct" prop_solvers_lpocircuits_direct
                             ]]
properties_circuits = [
              testGroup "Extended Circuits (Funsat)" [
                testProperty "direct" prop_ecircuitToCnf,
                testProperty "simplify(1)" prop_ecircuitToCnf_simp1,
                testProperty "simplify" prop_ecircuitToCnf_simp],
              testGroup "Circuits with naturals (funsat)" [
                testProperty "simplify nats: " prop_natcircuitToCnf_simp,
                testProperty "simplify nats(1): "  prop_natcircuitToCnf_simp1,
                testProperty "direct"  prop_natcircuitToCnf_direct],
              testGroup "Circuits with one predicates (funsat)" [
                testProperty "simplify : " prop_onecircuitToCnf_simp,
                testProperty "simplify (1): "  prop_onecircuitToCnf_simp1,
                testProperty "direct"  prop_onecircuitToCnf_direct],
              testGroup "LPO Circuits (funsat)" [
                testProperty "simplify one and nats: " prop_lpocircuitToCnf_simp,
                testProperty "simplify one: "  prop_lpocircuitToCnf_simp1,
                testProperty "direct"  prop_lpocircuitToCnf_direct],
              testGroup "LPO+status Circuits (funsat)" [
                testProperty "simplify one and nats: " prop_lposcircuitToCnf_simp,
                testProperty "simplify one: "  prop_lposcircuitToCnf_simp1,
                testProperty "direct"  prop_lposcircuitToCnf_direct],
              -- testGroup "MPO Circuits (funsat)" [
              --   testProperty "simplify one and nats: " prop_mpocircuitToCnf_simp,
              --   testProperty "simplify one: "  prop_mpocircuitToCnf_simp1,
              --   testProperty "direct"  prop_mpocircuitToCnf_direct],
              testGroup "Extended Circuits (Yices)" [
                testProperty "simplify 1" prop_ecircuitToCnf_simp1_yices,
                testProperty "simplify" prop_ecircuitToCnf_simp_yices,
                testProperty "direct" prop_ecircuitToCnf_direct_yices],
              testGroup "Circuits with naturals (Yices)" [
                testProperty "simplify nats: " prop_natcircuitToCnf_simp_yices,
                testProperty "simplify nats(1): "  prop_natcircuitToCnf_simp1_yices,
                testProperty "direct"  prop_natcircuitToCnf_direct_yices],
              testGroup "Circuits with one predicates (Yices)" [
                testProperty "simplify : " prop_onecircuitToCnf_simp_yices,
                testProperty "simplify (1): "  prop_onecircuitToCnf_simp1_yices,
                testProperty "direct"  prop_onecircuitToCnf_direct_yices],
              testGroup "LPO Circuits (Yices)" [
                testProperty "simplify all: " prop_lpocircuitToCnf_simp_yices,
                testProperty "simplify one: "  prop_lpocircuitToCnf_simp1_yices,
                testProperty "direct"  prop_lpocircuitToCnf_direct_yices],
              testGroup "LPO+Status Circuits (Yices)" [
                testProperty "simplify all: " prop_lposcircuitToCnf_simp_yices,
                testProperty "simplify one: "  prop_lposcircuitToCnf_simp1_yices,
                testProperty "direct"  prop_lposcircuitToCnf_direct_yices
                            ]
              ]

properties_various = [
              testGroup "Testing the tests" [
                testProperty "Enum NVar" (\(Positive i) -> fromEnum (toEnum i :: NVar) == i)
--                ,testProperty "Enum NVar(2)" (\(i::NVar) -> toEnum (fromEnum i) == i)
                            ]
             ]

check :: Testable a => a -> IO ()
check = quickCheckWith stdArgs { maxSuccess = 1000 }

-- -------------------------------
-- ** Circuits and CNF conversion
-- -------------------------------
type SizedGen a = Int -> Gen a

prop_ecircuitToCnf        = mkFunsatDirectProp (sizedECircuit :: SizedGen (Tree Id Var))
prop_ecircuitToCnf_simp   = mkFunsatSimpProp   (sizedECircuit :: SizedGen (Tree Id Var))
prop_ecircuitToCnf_simp1  = mkFunsatSimp1Prop  (sizedECircuit :: SizedGen (Tree Id Var))

prop_natcircuitToCnf_direct = mkFunsatDirectProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
prop_natcircuitToCnf_simp   = mkFunsatSimpProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
prop_natcircuitToCnf_simp1  = mkFunsatSimp1Prop (sizedNatCircuit :: SizedGen (Tree Id NVar))

prop_onecircuitToCnf_direct = mkFunsatDirectProp (sizedOneCircuit :: SizedGen (Tree Id Var))
prop_onecircuitToCnf_simp   = mkFunsatSimpProp (sizedOneCircuit :: SizedGen (Tree Id Var))
prop_onecircuitToCnf_simp1  = mkFunsatSimp1Prop (sizedOneCircuit :: SizedGen (Tree Id Var))

prop_lpocircuitToCnf_direct   = mkFunsatDirectRPOProp sizedLPOCircuit
prop_lpocircuitToCnf_simp     = mkFunsatSimpRPOProp   sizedLPOCircuit
prop_lpocircuitToCnf_simp1    = mkFunsatSimp1RPOProp  sizedLPOCircuit

prop_lposcircuitToCnf_direct   = mkFunsatDirectRPOProp sizedLPOsCircuit
prop_lposcircuitToCnf_simp     = mkFunsatSimpRPOProp   sizedLPOsCircuit
prop_lposcircuitToCnf_simp1    = mkFunsatSimp1RPOProp  sizedLPOsCircuit

prop_mpocircuitToCnf_direct   = mkFunsatDirectRPOProp sizedMPOCircuit
prop_mpocircuitToCnf_simp     = mkFunsatSimpRPOProp   sizedMPOCircuit
prop_mpocircuitToCnf_simp1    = mkFunsatSimp1RPOProp  sizedMPOCircuit

prop_ecircuitToCnf_direct_yices = mkYicesDirectProp (sizedECircuit :: SizedGen (Tree Id Var))
prop_ecircuitToCnf_simp_yices   = mkYicesSimpProp   (sizedECircuit :: SizedGen (Tree Id Var))
prop_ecircuitToCnf_simp1_yices  = mkYicesSimp1Prop  (sizedECircuit :: SizedGen (Tree Id Var))

prop_natcircuitToCnf_direct_yices = mkYicesDirectProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
prop_natcircuitToCnf_simp_yices   = mkYicesSimpProp (sizedNatCircuit :: SizedGen (Tree Id NVar))
prop_natcircuitToCnf_simp1_yices  = mkYicesSimp1Prop (sizedNatCircuit :: SizedGen (Tree Id NVar))

prop_onecircuitToCnf_direct_yices = mkYicesDirectProp (sizedOneCircuit :: SizedGen (Tree Id Var))
prop_onecircuitToCnf_simp_yices   = mkYicesSimpProp (sizedOneCircuit :: SizedGen (Tree Id Var))
prop_onecircuitToCnf_simp1_yices  = mkYicesSimp1Prop (sizedOneCircuit :: SizedGen (Tree Id Var))

prop_lpocircuitToCnf_direct_yices = mkYicesDirectRPOProp sizedLPOCircuit
prop_lpocircuitToCnf_simp_yices   = mkYicesSimpRPOProp   sizedLPOCircuit
prop_lpocircuitToCnf_simp1_yices  = mkYicesSimp1RPOProp  sizedLPOCircuit

prop_lposcircuitToCnf_direct_yices = mkYicesDirectRPOProp sizedLPOsCircuit
prop_lposcircuitToCnf_simp_yices   = mkYicesSimpRPOProp   sizedLPOsCircuit
prop_lposcircuitToCnf_simp1_yices  = mkYicesSimp1RPOProp  sizedLPOsCircuit

trivial pred = classify pred "Trivial"

instance OneCircuit ECircuit.Shared

mkFunsatSimpProp :: forall id v.
                    ( Ord v, HasTrie v, Show v, Bounded v, Enum v
                    , Ord id, HasTrie id, Show id
                    ) => SizedGen (Tree id v) -> Property
mkFunsatSimpProp gen = forAll (sized gen) $ \c ->
    let pblm@(CircuitProblem{ problemCnf = cnf })
           = toCNF
           . (runShared :: Shared id v -> FrozenShared id v)
           . castCircuit $ c
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectCircuitSolution solution pblm
                      benv' = benv `mappend` Map.fromList [(v,False) | v <- toList c]
                  in   label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castCircuit c)

         Unsat{} -> label "Unsat (unverified)" True

mkFunsatSimp1Prop :: forall id v.
                     ( Ord v, HasTrie v, Show v, Bounded v, Enum v
                     , Ord id, Show id, HasTrie id
                     ) => SizedGen (Tree id v) -> Property
mkFunsatSimp1Prop gen = forAll (sized gen) $ \c ->
    let pblm = unsafePerformIO
             . toCNFBS
             . (runShared :: Shared id v -> FrozenShared id v)
             . castCircuit $ c
        (solution,_,_) = solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" . asDimacs . eproblemCnf $ pblm
    in case solution of
         Sat{} -> let benv = projectECircuitSolution solution pblm
                      benv' = benv `mappend` Map.fromList [(v,False) | v <- toList c]
                  in label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castCircuit c)

         Unsat{} -> label "Unsat (unverified)" True


mkFunsatDirectProp :: forall id v.
                      (Ord v, HasTrie v, Show v, Bounded v, Enum v
                      ,Ord id, Show id, HasTrie id
                      ) => SizedGen (Tree id v) -> Property
mkFunsatDirectProp gen = forAll (sized gen) $ \c ->
    let pblm = unsafePerformIO
             . toCNFRPO
             . (runShared :: Shared id v -> FrozenShared id v)
             . castCircuit $ c
        (solution,_,_) = solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" . asDimacs . rpoProblemCnf
                       $ pblm
    in case solution of
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                      benv' = benv `mappend` Map.fromList [(v,False) | v <- toList c]
                  in label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castCircuit c)

         Unsat{} -> label "Unsat (unverified)" True
{-
mkFunsatSimpRPOProp :: forall v id.
                       (Ord v, HasTrie v, Show v, Bounded v, Enum v
                       ,Ord id, Pretty id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ,RPOExtCircuit (Shared id) id
                       ) => SizedGen (Tree id v) -> Property
-}
mkFunsatSimpRPOProp gen = forAll (sized gen) mkFunsatSimpRPOProp'
mkFunsatSimpRPOProp' c  =
    let pblm@(CircuitProblem{ problemCnf = cnf })
           = toCNF
           . runShared
--           . (castRPOCircuit :: Tree id v -> Shared id v)
           . (castRPOCircuit :: (Ord v, HasTrie v, Show v, RPOExtCircuit (Shared id) id, Ord id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id) => Tree id v -> Shared id v)
           $ c
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectCircuitSolution solution pblm
                      benv' = benv `mappend` Map.fromList [(v,False) | v <- toList c]
                  in   label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castRPOCircuit c)

         Unsat{} -> label "Unsat (unverified)" True

mkFunsatSimp1RPOProp gen = forAll (sized gen) mkFunsatSimp1RPOProp'
mkFunsatSimp1RPOProp' c  =
    let pblm = unsafePerformIO
             . toCNFBS
             . runShared
             . (castRPOCircuit :: (Ord v, HasTrie v, Show v, RPOExtCircuit (Shared id) id, Ord id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id) => Tree id v -> Shared id v)
             $ c
        (solution,_,_) = solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" . asDimacs . eproblemCnf $ pblm
    in case solution of
         Sat{} -> let benv = projectECircuitSolution solution pblm
                      benv' = benv `mappend` Map.fromList [(v,False) | v <- toList c]
                  in label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castRPOCircuit c)

         Unsat{} -> label "Unsat (unverified)" True

mkFunsatDirectRPOProp gen = forAll (sized gen) mkFunsatDirectRPOProp'
mkFunsatDirectRPOProp' c =
    let pblm = unsafePerformIO
             . toCNFRPO
             . runShared
             . (castRPOCircuit :: (Ord v, HasTrie v, Show v, RPOExtCircuit (Shared id) id, Ord id, Show id, HasPrecedence v id, HasFiltering v id, HasStatus v id) => Tree id v -> Shared id v)
             $ c
        (solution,_,_) = solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" . asDimacs . rpoProblemCnf
                       $ pblm
    in case solution of
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                      benv' = benv `mappend` Map.fromList [(v,False) | v <- toList c]
                  in label "Sat"
                     . trivial (Map.null benv)
                     $ fromRight $ runEval benv' (castRPOCircuit c)

         Unsat{} -> label "Unsat (unverified)" True


mkYicesDirectProp :: forall id v.
                     (Ord v, HasTrie v, Show v, Bounded v, Enum v
                     ,Ord id, Show id, HasTrie id
                     ) => SizedGen (Tree id v) -> Property
mkYicesDirectProp gen = forAll (sized gen) $ \c ->
    let correct = unsafePerformIO $
                  solveYicesDirect defaultYicesOpts
                    ((assert [castCircuit c]  :: SAT id v ()) >>
                     return (evalB (castCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimpProp :: forall id v.
                   (Ord v, HasTrie v, Show v, Bounded v, Enum v
                   ,Ord id, Show id, HasTrie id
                   ) => SizedGen (Tree id v) -> Property
mkYicesSimpProp gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  solveYicesSimp defaultYicesOpts
                    ((assert [castCircuit c]  :: SAT id v ()) >>
                     return (evalB (castCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimp1Prop :: forall id v.
                    (Ord v, HasTrie v, Show v, Bounded v, Enum v
                    ,Ord id, Show id, HasTrie id
                    ) => SizedGen (Tree id v) -> Property
mkYicesSimp1Prop gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  solveYicesSimp1 defaultYicesOpts
                    ((assert [castCircuit c]  :: SAT id v ()) >>
                     return (evalB (castCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x


mkYicesDirectRPOProp :: forall id v. ( Ord v, HasTrie v, Show v, Bounded v, Enum v
                                     , Ord id, Pretty id, Show id, HasTrie id
                                     , HasPrecedence v id, HasFiltering v id, HasStatus v id
                                     , RPOExtCircuit (Shared id) id
                                     ) => SizedGen (Tree id v) -> Property
mkYicesDirectRPOProp gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  solveYicesDirect defaultYicesOpts
                    (assert [castRPOCircuit c]  >>
                     return (evalB (castRPOCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimpRPOProp :: forall id v.
                      (Ord v, HasTrie v, Show v, Bounded v, Enum v
                      ,Ord id, HasTrie id, Show id, Pretty id
                      ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                      ,RPOExtCircuit (Shared id) id
                      ) => SizedGen (Tree id v) -> Property
mkYicesSimpRPOProp gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  solveYicesSimp defaultYicesOpts
                    (assert [castRPOCircuit c :: Shared id v] >>
                     return (evalB (castRPOCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x

mkYicesSimp1RPOProp :: forall id v.
                       (Ord v, HasTrie v, Show v, Bounded v, Enum v
                       ,Ord id, HasTrie id, Show id, Pretty id
                       ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                       ,RPOExtCircuit (Shared id) id
                       ) => SizedGen (Tree id v) -> Property
mkYicesSimp1RPOProp gen = forAll (sized gen) $ \(c :: Tree id v) ->
    let correct = unsafePerformIO $
                  solveYicesSimp1 defaultYicesOpts
                    (assert [castCircuit c :: Shared id v] >>
                     return (evalB (castRPOCircuit c)))
    in case correct of
         Nothing -> label "Unsat" True
         Just x  -> label "Sat" x
-- --------------------
-- Solver sanity checks
-- --------------------
prop_solvers_ecircuits_simp = forAll (sized sizedECircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_ecircuits_direct = forAll (sized sizedECircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp1 defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_ecircuits_directRPO = forAll (sized sizedECircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesDirect defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_natcircuits_simp = forAll (sized sizedNatCircuit) $ \(c :: Tree Id NVar) ->
  let shrd  = castCircuit c :: Shared Id NVar
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_natcircuits_direct = forAll (sized sizedNatCircuit) $ \(c :: Tree Id NVar) ->
  let shrd  = castCircuit c :: Shared Id NVar
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp1 defaultYicesOpts (assert [shrd] :: SAT Id NVar ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_natcircuits_directRPO = forAll (sized sizedNatCircuit) $ \(c :: Tree Id NVar) ->
  let shrd  = castCircuit c :: Shared Id NVar
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesDirect defaultYicesOpts (assert [shrd] :: SAT Id NVar ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_onecircuits_simp = forAll (sized sizedOneCircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_onecircuits_direct = forAll (sized sizedOneCircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp1 defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_onecircuits_directRPO = forAll (sized sizedOneCircuit) $ \(c :: Tree Id Var) ->
  let shrd  = castCircuit c :: Shared Id Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesDirect defaultYicesOpts (assert [shrd] :: SAT Id Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_lpocircuits_simp = forAll (sized sizedLPOCircuit) $ \(c :: Tree LDPId Var) ->
  let shrd  = castRPOCircuit c :: Shared LDPId Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp defaultYicesOpts (assert [shrd])
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_lpocircuits_simp1 = forAll (sized sizedLPOCircuit) $ \(c :: Tree LDPId Var) ->
  let shrd  = castRPOCircuit c :: Shared LDPId Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesSimp1 defaultYicesOpts (assert [shrd] :: SAT LDPId Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

prop_solvers_lpocircuits_direct = forAll (sized sizedLPOCircuit) $ \(c :: Tree LDPId Var) ->
  let shrd  = castRPOCircuit c :: Shared LDPId Var
      pblm  = toCNF $ runShared shrd
      (sol,_,_) = solve1 $ problemCnf pblm
      yicesSol = liftM snd $ unsafePerformIO $
                 runYicesDirect defaultYicesOpts (assert [shrd] :: SAT LDPId Var ())
  in trivial (isUnsat sol) $  if isUnsat sol then isNothing yicesSol else isJust yicesSol

isUnsat Sat{} = False
isUnsat Unsat{} = True

-- -----------------------
-- RPO order comparisons
-- -----------------------

prop_lporuleGtToCNF_simp :: RuleN Id -> Property
prop_lporuleGtToCNF_simp = mkRuleGtProp lpo solveFun . (:[])

prop_lporuleGtToCNF_direct_yices :: RuleN Id -> Property
prop_lporuleGtToCNF_direct_yices = mkRuleGtProp lpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing)) . (:[])

prop_lporuleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_lporuleGtToCNF_simp1_yices = mkRuleGtProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])

prop_lporuleGtToCNF_simp_yices :: RuleN Id -> Property
prop_lporuleGtToCNF_simp_yices = mkRuleGtProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])

prop_lporuleEqToCNF_simp :: RuleN Id -> Property
prop_lporuleEqToCNF_simp = mkRuleEqProp lpo solveFun . (:[])

prop_lporuleEqToCNF_direct_yices :: RuleN Id -> Property
prop_lporuleEqToCNF_direct_yices = mkRuleEqProp lpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing)) . (:[])

prop_lporuleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_lporuleEqToCNF_simp1_yices = mkRuleEqProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])

prop_lporuleEqToCNF_simp_yices :: RuleN Id -> Property
prop_lporuleEqToCNF_simp_yices = mkRuleEqProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])


prop_lporulesGtToCNF_simp :: [RuleN Id] -> Property
prop_lporulesGtToCNF_simp = mkRuleGtProp lpo solveFun

prop_lporulesGtToCNF_direct :: [RuleN Id] -> Property
prop_lporulesGtToCNF_direct = mkRuleGtProp lpo solveFunDirect

prop_lporulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_lporulesGtToCNF_direct_yices = mkRuleGtProp lpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing))

prop_lporulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_lporulesGtToCNF_simp1_yices = mkRuleGtProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

prop_lporulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_lporulesGtToCNF_simp_yices = mkRuleGtProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

prop_lporulesEqToCNF_simp :: [RuleN Id] -> Property
prop_lporulesEqToCNF_simp = mkRuleEqProp lpo solveFun

prop_lporulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_lporulesEqToCNF_direct_yices = mkRuleEqProp lpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing))

prop_lporulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_lporulesEqToCNF_simp1_yices = mkRuleEqProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

prop_lporulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_lporulesEqToCNF_simp_yices = mkRuleEqProp lpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))


prop_mporuleGtToCNF_simp :: RuleN Id -> Property
prop_mporuleGtToCNF_simp = mkRuleGtProp mpo solveFun . (:[])

prop_mporuleGtToCNF_direct :: RuleN Id -> Property
prop_mporuleGtToCNF_direct = mkRuleGtProp mpo solveFunDirect . (:[])

prop_mporuleGtToCNF_direct_yices :: RuleN Id -> Property
prop_mporuleGtToCNF_direct_yices = mkRuleGtProp mpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing)) . (:[])

prop_mporuleGtToCNF_simp1_yices :: RuleN Id -> Property
prop_mporuleGtToCNF_simp1_yices = mkRuleGtProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])

prop_mporuleGtToCNF_simp_yices :: RuleN Id -> Property
prop_mporuleGtToCNF_simp_yices = mkRuleGtProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])

prop_mporuleEqToCNF_simp :: RuleN Id -> Property
prop_mporuleEqToCNF_simp = mkRuleEqProp mpo solveFun . (:[])

prop_mporuleEqToCNF_direct :: RuleN Id -> Property
prop_mporuleEqToCNF_direct = mkRuleEqProp mpo solveFunDirect . (:[])

prop_mporuleEqToCNF_direct_yices :: RuleN Id -> Property
prop_mporuleEqToCNF_direct_yices = mkRuleEqProp mpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing)) . (:[])

prop_mporuleEqToCNF_simp1_yices :: RuleN Id -> Property
prop_mporuleEqToCNF_simp1_yices = mkRuleEqProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])

prop_mporuleEqToCNF_simp_yices :: RuleN Id -> Property
prop_mporuleEqToCNF_simp_yices = mkRuleEqProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing)) . (:[])


prop_mporulesGtToCNF_simp :: [RuleN Id] -> Property
prop_mporulesGtToCNF_simp = mkRuleGtProp mpo solveFun

prop_mporulesGtToCNF_direct :: [RuleN Id] -> Property
prop_mporulesGtToCNF_direct = mkRuleGtProp mpo solveFunDirect

prop_mporulesGtToCNF_direct_yices :: [RuleN Id] -> Property
prop_mporulesGtToCNF_direct_yices = mkRuleGtProp mpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing))

prop_mporulesGtToCNF_simp1_yices :: [RuleN Id] -> Property
prop_mporulesGtToCNF_simp1_yices = mkRuleGtProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

prop_mporulesGtToCNF_simp_yices :: [RuleN Id] -> Property
prop_mporulesGtToCNF_simp_yices = mkRuleGtProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

prop_mporulesEqToCNF_simp :: [RuleN Id] -> Property
prop_mporulesEqToCNF_simp = mkRuleEqProp mpo solveFun

prop_mporulesEqToCNF_direct :: [RuleN Id] -> Property
prop_mporulesEqToCNF_direct = mkRuleEqProp mpo solveFunDirect

prop_mporulesEqToCNF_direct_yices :: [RuleN Id] -> Property
prop_mporulesEqToCNF_direct_yices = mkRuleEqProp mpo (unsafePerformIO . solveYicesDirect (YicesOpts 20 Nothing))

prop_mporulesEqToCNF_simp1_yices :: [RuleN Id] -> Property
prop_mporulesEqToCNF_simp1_yices = mkRuleEqProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

prop_mporulesEqToCNF_simp_yices :: [RuleN Id] -> Property
prop_mporulesEqToCNF_simp_yices = mkRuleEqProp mpo (unsafePerformIO . solveYicesSimp1 (YicesOpts 20 Nothing))

-- ---------------------------------------
-- helpers for interactive testing in GHCi
-- ---------------------------------------
{-
testRulePropYicesDirect ext rules k = solveYicesDirect (YicesOpts 20 Nothing)
                                                  (mkSymbolRules ext rules >>= detailedOutputFor k)
testRulePropYicesSimp1  ext rules k = solveYicesSimp1 (YicesOpts 20 Nothing)
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

testRulePropDirect', testRulePropSimp' ::
              (sid ~ symb Var DPId, HasTrie sid, Ord sid, Show sid, Pretty sid)
              => SymbolFactory symb
              -> [RuleN Id]
              -> ( [RuleN sid] -> SAT sid Var (EvalM Var a) )
              -> IO (Maybe (Map Var Bool   -- Var mapping
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
        pblm = unsafePerformIO
             . toCNFRPO
             $ frozen
        (solution,_,_) = solve1 . asCNF . either (error.show) id
                       . ParseCNF.parseByteString "input" . asDimacs . rpoProblemCnf
                       $ pblm

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
         Sat{} -> let benv = projectRPOCircuitSolution solution pblm
                  in return $ Just (benv, symbols, runEvalM benv res)

         Unsat{} -> return Nothing

testRulePropSimp' ext rules k = do
    let SAT satComp = do
          symbols <- mkSymbolRules ext rules
--          (coherent, correct) <- liftM ((Prelude.and *** Prelude.and) . unzip) $ mapM k symbols
          res <- k symbols
          return (res, symbols)
        ((res, symbols), St _ circuit _weighted) = runState satComp (St [V 1 ..] true [])
        frozen = runShared circuit
        pblm = toCNF frozen
        (solution,_,_) = solve1 $ problemCnf pblm

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
         Sat{} -> let benv = projectCircuitSolution solution pblm
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


mkRuleGtProp :: (id ~ symb Var DPId, Ord id, Pretty id, RPOExtCircuit (Shared id) id
                ,HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                ) => SymbolFactory symb -> (SAT id Var (EvalM Var Bool) -> Maybe Bool) -> [RuleN Id] -> Property
mkRuleGtProp ext solve rules
  = case solve result of
     Nothing -> label "unsat" True
     Just b  -> property b
 where
   result = do rr <- mkSymbolRules ext rules
               assert [foldr and true [l `termGt` r | l:->r <- rr]]
               return $ evalB (foldr and true [l `termGt` r | l:->r <- rr])

mkRuleEqProp :: (id ~ symb Var DPId, Ord id, Pretty id, RPOExtCircuit (Shared id) id
                ,HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                ) => SymbolFactory symb -> (SAT id Var (EvalM Var Bool) -> Maybe Bool) -> [RuleN Id] -> Property
mkRuleEqProp ext solve rules
  = case solve result of
     Nothing -> label "unsat" True
     Just b  -> property b
 where
   result = do rr <- mkSymbolRules ext rules
               assert [foldr and true [l `termEq` r | l:->r <- rr]]
               return $ evalB (foldr and true [l `termEq` r | l:->r <- rr])

mkSymbolRules :: (id ~ symb Var DPId) => SymbolFactory symb -> [RuleN Id] -> SAT id Var [RuleN id]
--mkSymbolRules :: [RuleN Id] -> SAT id Var [RuleN LDPId]
mkSymbolRules ext rr = do
     let symbols = toList $ getAllSymbols rr
     symbols'   <- mapM (mkSATSymbol ext) symbols
     let convert = fromJust . (`Map.lookup` dict)
         dict    = Map.fromList (zip symbols symbols')
         rr_s    = (fmap.fmap) (mapTermSymbols convert) rr
     return rr_s
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


test_circuitToCnf :: forall id. (HasTrie id, Ord id) => [Eval NVar] -> Tree id NVar -> IO ()
test_circuitToCnf vars treeCircuit =
    let pblm@(CircuitProblem{ problemCnf = cnf }) =
            toCNF $ runShared (castCircuit treeCircuit :: Shared id NVar)
        (solution, _, _) = solve1 cnf
    in case solution of
         Sat{} -> let benv = projectCircuitSolution solution pblm
                  in do print $ map (runEval benv) vars
                        putStrLn ""
                        print $ fromRight $ runEval benv (castCircuit treeCircuit)

         Unsat{} -> putStrLn "Unsat"

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

data NVar = VN Int | VB Int deriving (Eq, Ord, Show)

mkNat bb = ECircuit.nat . map VN $ bb
vb i     = input $ VB i

instance Bounded NVar where minBound = VN 0; maxBound = VB maxBound
instance Enum NVar where
  fromEnum (VN i) = i * 2
  fromEnum (VB i) = (i * 2) + 1
  toEnum i = (if odd i then VB else VN) (i `div` 2)
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
          , return $ eq (mkNat [0..n`div`2]) (mkNat [succ (n`div`2) .. n])
          , return $ lt (mkNat [0..n`div`2]) (mkNat [succ (n`div`2) .. n])
          ]
  where subcircuit2  = sizedNatCircuit (n `div` 2)
        subcircuit1  = sizedNatCircuit (n - 1)
        subcircuit2' = (fmap.fmap) convert $ sizedCircuit (n `div` 2)
        convert (V i)= VB i

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
          , return $ eq (mkNat [0..n`div`2]) (mkNat [succ (n`div`2) .. n])
          , return $ lt (mkNat [0..n`div`2]) (mkNat [succ (n`div`2) .. n])
          , return $ one (map (input.VB) [0..n])
          ]
  where subcircuit3  = sizedOneNatECircuit (n `div` 3)
        subcircuit2  = sizedOneNatECircuit (n `div` 2)
        subcircuit1  = sizedOneNatECircuit (n - 1)
        subcircuit2' = (fmap.fmap) vb $ sizedOneCircuit (n `div` 2)
        subcircuit3' = (fmap.fmap) vb $ sizedOneCircuit (n `div` 3)
        mkNat        = ECircuit.nat . map VN
        vb (V i)     = VB i


sizedLPOCircuit :: forall c. RPOCircuit c LDPId => Int -> Gen (c Var)
sizedLPOCircuit = sizedxPOCircuit undefined -- :: LPOsymbol Var DPId)

sizedMPOCircuit :: forall c. RPOCircuit c (MPOsymbol Var DPId) => Int -> Gen (c Var)
sizedMPOCircuit = sizedxPOCircuit undefined

sizedLPOsCircuit :: forall c. RPOCircuit c (LPOSsymbol Var DPId) => Int -> Gen (c Var)
sizedLPOsCircuit = sizedxPOCircuit undefined -- :: LPOSsymbol Var DPId)

type Proxy a = a

sizedxPOCircuit :: forall c (lpoid :: * -> * -> *) id.
                   (HasPrecedence Var id, HasStatus Var id, HasFiltering Var id
                   ,id ~ lpoid Var (DPIdentifier Id)
                   ,Ord id, HasTrie id
                   ,RPOCircuit c id
                   ,Arbitrary (SAT' Id lpoid Var (RuleN id))
                   ) => Proxy id -> Int -> Gen (c Var)
sizedxPOCircuit _ = liftM (uncurry and . second (removeComplex'.runShared) . runSAT') . go where
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
shrinkTree (TNat (_:bb)) = [TNat bb]
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
shrinkETree (ECircuit.TNat (_:bb)) = [ECircuit.TNat bb]
shrinkETree t = []

data Id = F | G | S | Z deriving (Eq, Ord, Show)
instance Pretty Id where pPrint = text . show
instance HasTrie Id where
  data Id :->: x = IdTrie (Maybe x) (Maybe x) (Maybe x) (Maybe x)
  empty = IdTrie Nothing Nothing Nothing Nothing
  lookup F (IdTrie f _ _ _) = f
  lookup G (IdTrie _ g _ _) = g
  lookup S (IdTrie _ _ s _) = s
  lookup Z (IdTrie _ _ _ z) = z
  insert F v (IdTrie f g s z) = IdTrie (Just v) g s z
  insert G v (IdTrie f g s z) = IdTrie f (Just v) s z
  insert S v (IdTrie f g s z) = IdTrie f g (Just v) z
  insert Z v (IdTrie f g s z) = IdTrie f g s (Just v)
  toList (IdTrie f g s z) = catMaybes [(,) F `fmap` f
                                      ,(,) G `fmap` g
                                      ,(,) S `fmap` s
                                      ,(,) Z `fmap` z]


-- Generating Terms

type DPId  = DPIdentifier Id
type LPOId = LPOsymbol NVar Id
type LDPId = LPOsymbol Var DPId
type RDPId = SymbolRes DPId

instance Arbitrary Id
 where
  arbitrary = elements [F,G,S,Z]

--instance Arbitrary DPId where arbitrary = elements [IdDP F, IdDP G, IdFunction S, IdFunction Z]

class IsDefined id where isDefined :: id -> Bool

instance IsDefined Id where
 isDefined F = True
 isDefined G = True
 isDefined _ = False

instance HasArity Id where
  getIdArity F = 1
  getIdArity G = 1
  getIdArity S = 1
  getIdArity Z = 0

instance IsDefined a => IsDefined (RPOSsymbol v a) where isDefined = isDefined . theSymbol
deriving instance IsDefined a => IsDefined (LPOsymbol v a)
deriving instance IsDefined a => IsDefined (MPOsymbol v a)
deriving instance IsDefined a => IsDefined (RPOsymbol v a)
deriving instance IsDefined a => IsDefined (LPOSsymbol v a)

mkSATSymbol mk F = mk 2 (IdFunction F, 1, True)
mkSATSymbol mk G = mk 2 (IdFunction G, 1, True)
mkSATSymbol mk S = mk 2 (IdFunction S, 1, False)
mkSATSymbol mk Z = mk 2 (IdFunction Z, 0,False)


mkSymbol F = createSymbol 0 0 F 1
mkSymbol G = createSymbol 5 2 G 1
mkSymbol S = createSymbol 10 4 S 1
mkSymbol Z = createSymbol 15 6 Z 0

createSymbol :: Int -> Int -> id -> Int -> LPOsymbol NVar id
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
  prec = Natural [vn 1, vn 2]

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
  prec = Natural [vn 1, vn 2]

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

instance (HasArity id, IsDefined id, Arbitrary id) => Arbitrary (RuleN id)
  where
   arbitrary = do
      lhs <- sized sizedDefTerm
      rhs <- sized sizedTerm
      return ( lhs :-> rhs )

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

runSAT' = second circuit . (`runState` st0{pool=[V 1000..]}) . unSAT . (`evalStateT` Map.empty)

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
