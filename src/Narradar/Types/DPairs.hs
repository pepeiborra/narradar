
{-# LANGUAGE ScopedTypeVariables, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Narradar.Types.DPairs where

import Control.Exception (assert)
import qualified Data.Array.IArray as A
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude as P hiding (pi)
import qualified TRSParser as TRS
import qualified TRSTypes  as TRS
import TRSTypes hiding (Id, Term, Narrowing, SimpleRuleF(..))
import Text.ParserCombinators.Parsec (runParser)


import Narradar.Constraints.VariableCondition
import Narradar.Types.ArgumentFiltering (AF_, PolyHeuristicN, MkHeu, mkHeu, isSoundAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.ProblemType
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Utils.Convert
import Narradar.Utils.Ppr
import Lattice

-- -----------------
-- Parsing TPDB TRSs
-- -----------------
-- Here to avoid introducing recursive module dependencies

parseTRS :: Monad m => String -> m (Problem Id Var)
parseTRS = eitherM . runParser trsParser mempty "<input>"

trsParser :: TRS.TRSParser (Problem Id Var)
trsParser = do
  Spec spec <- TRS.trsParser
  let r = mkTRS $ concat [mkRules rr | Rules rr <- spec]
      p = concat [mkDPs   rr | Pairs rr <- spec]
      mkStrat                                              :: Monad m => TRS.Strategy -> m (ProblemType Id)
      mkStrat InnerMost                                    = return InnermostRewriting
      mkStrat OuterMost                                    = return Rewriting
      mkStrat TRS.Narrowing                                = return Narrowing
      mkStrat ConstructorNarrowing                         = return GNarrowing
      mkStrat BasicNarrowing                               = return BNarrowing
      mkStrat (TRS.NarrowingG            (TRS.Term id tt)) = return (narrowingModes  r (id,tt))
      mkStrat (TRS.BasicNarrowingG       (TRS.Term id tt)) = return (bNarrowingModes r (id,tt))
      mkStrat (TRS.ConstructorNarrowingG (TRS.Term id tt)) = return (gNarrowingModes r (id,tt))
      mkStrat s                                            = fail ("Unknown strategy: " ++ show s)

  strategy <- maybe (return Rewriting) mkStrat $ listToMaybe [s | Strategy s <- spec]
  return $ case p of
     [] -> mkDPProblem strategy r
     _  -> let r' = convert r in mkProblem strategy r' (dpTRS (Problem (convert strategy) r' (tRS p)) emptyArray)
          -- TODO Consider goal problems when the PAIRS set is not empty
 where
  mkDPs   rr = map markDPRule (convert $ mkRules rr)
  mkRules rr = [ toTerm l :-> toTerm r | Rule (l TRS.:-> r) _ <- rr] where
           toTerm = foldTerm toVar (Impure . fromSimple)
           allvars = Map.fromList (Set.toList(getVars rr) `zip` [0..])
           toVar v = var' (Just v) (fromJust $ Map.lookup v allvars)


-- -------------------------
-- Constructing DP problems
-- -------------------------

-- THERE IS A SERIOUS BUG IN GHC 6.10.1 WITH INSTANCE RESOLUTION IN PRESENCE OF TYPE FUNCTIONS AND OVERLOADING
-- IT IS NO LONGER TRUE THAT THE MOST SPECIFIC INSTANCE IS PICKED, SINCE TYPE EXPRESSIONS ARE NOT REDUCED
-- SO STAY AWAY FROM TYPE FUNCTIONS FOR NOW !!!!!!!!!!!!

-- | Constructing DP problems. Do not construct a goal problem with this function, for that use 'mkGoalProblem'
mkDPProblem :: (Ppr id, Ord a, id ~ Identifier a, RemovePrologId a) => ProblemType id -> NarradarTRS a Var -> Problem id Var
mkDPProblem typ _ | isModed typ = error "To create a goal problem use 'mkGoalProblem'"
mkDPProblem typ trs = mkProblem typ trs' (mkDPs typ trs') where trs' = convert trs

-- | Construct the set of pairs corresponding to a problem type and a TRS R of rules.
mkDPs :: (Ord a, id ~ Identifier a) => ProblemType id -> NarradarTRS id Var -> NarradarTRS id Var
mkDPs typ trs
    | isFullNarrowing typ = dpTRS (Problem typ trs (tRS $ getNPairs trs)) emptyArray
    | otherwise           = dpTRS (Problem typ trs (tRS $ getPairs  trs)) emptyArray

-- | Constructing NDP problems with as starting goal. This function takes an AF heuristic.
--   This is necessary so early because before splitting P into SCCs we need to ensure
--   that P is indeed a TRS (no extra variables).
--   I.e. we need to compute the filtering 'globally'
mkGoalProblem :: (Ppr id, Ord a, PolyHeuristicN heu id, Lattice (AF_ id), RemovePrologId a, id ~ Identifier a) =>
                 MkHeu heu -> ProblemType a -> NarradarTRS a Var -> [Problem id Var]
mkGoalProblem heu typ trs =
    let trs'       = convert trs
        dps        = mkDPs typ' trs'
        typ'       = typ{pi=extendedPi, goal=AF.extendToTupleSymbols (goal typ)}
        extendedPi = AF.extendToTupleSymbols (pi typ)
        p0         = mkProblem typ' trs' dps
        orProblems = case mkHeu heu p0 of
                       heu -> [assert (isSoundAF pi' p0) $
                               mkProblem typ'{pi=pi'} trs' dps
                                   | pi' <- Set.toList $ invariantEV heu (rules p0) extendedPi]
    in assert (not $ null orProblems) orProblems

-- ---------------------------
-- Computing Dependency Pairs
-- ---------------------------
--getPairs :: (Ord id, Ord v) => NarradarTRS id v -> [DP (TermF (Identifier id)) v]
getPairs trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isRootDefined trs) r]

--getNPairs :: (Ord id, Ord v) => NarradarTRS id v -> [DP (TermF (Identifier id)) v]
getNPairs trs = getPairs trs ++ getLPairs trs

--getLPairs :: (Ord id, Ord v) => NarradarTRS id v -> [DP (TermF (Identifier id)) v]
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isRootDefined trs lp]


-------------------------
emptyArray = A.listArray (0,-1) []
