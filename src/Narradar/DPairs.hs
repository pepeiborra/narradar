
{-# LANGUAGE ScopedTypeVariables, PatternGuards, ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Narradar.DPairs where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.State
import qualified Data.Array.IArray as A
import qualified Data.Graph as G
import Data.List ((\\))
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable as T
import qualified Data.Tree as Tree
import Text.XHtml (toHtml, Html)
import Prelude as P hiding (pi)

import TRS
import Control.Monad.MonadSupply
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Types
import Narradar.Utils
import Narradar.Proof
import Narradar.ExtraVars

-- THERE IS A SERIOUS BUG IN GHC 6.10.1 WITH INSTANCE RESOLUTION IN PRESENCE OF TYPE FUNCTIONS AND OVERLOADING
-- IT IS NO LONGER TRUE THAT THE MOST SPECIFIC INSTANCE IS PICKED, SINCE TYPE EXPRESSIONS ARE NOT REDUCED
-- SO STAY AWAY FROM TYPE FUNCTIONS FOR NOW !!!!!!!!!!!!

--mkDPProblem :: (DPMark (DPVersionOf f), TRSC f, T id :<: f, T (Identifier id) :<: DPVersionOf f, Convert (Term f) (Term (DPVersionOf f)), TRSC (DPVersionOf f), Show (Identifier id), Ord id) => ProblemType id -> NarradarTRS id f -> ProblemG (Identifier id) (DPVersionOf f)
mkDPProblem :: (DPMark (DPVersionOf f), TRSC f, T id :<: f, T (Identifier id) :<: f', Convert (Term f) (Term f'), TRSC f', Show (Identifier id), Ord id, DPMark f') => ProblemType id -> NarradarTRS id f -> ProblemG (Identifier id) f'
mkDPProblem Rewriting   trs = let trs' = convert trs in mkProblem Rewriting   trs' (tRS $ getPairs trs')
mkDPProblem Narrowing   trs = let trs' = convert trs in mkProblem Narrowing   trs' (tRS $ getNPairs trs')
mkDPProblem BNarrowing  trs = let trs' = convert trs in mkProblem BNarrowing  trs' (tRS $ getPairs trs')
mkDPProblem GNarrowing  trs = let trs' = convert trs in mkProblem GNarrowing  trs' (tRS $ getPairs trs')
mkDPProblem LBNarrowing trs = let trs' = convert trs in mkProblem LBNarrowing trs' (tRS $ getPairs trs')

getPairs :: (Ord id, T id :<: f, DPMark f) => NarradarTRS id f -> [DP f]
getPairs trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isDefined trs) r]

getNPairs :: (Ord id, T id :<: f, DPMark f) => NarradarTRS id f -> [DP f]
getNPairs trs = getPairs trs ++ getLPairs trs

getLPairs :: (Ord id, T id :<: f, DPMark f) => NarradarTRS id f -> [DP f]
getLPairs trs = [ markDP l :-> markDP lp | l :-> _ <- rules trs, lp <- properSubterms l, isDefined trs lp]


{-# SPECIALIZE cycleProcessor :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE sccProcessor   :: Problem BBasicId -> ProblemProof Html BBasicId #-}
cycleProcessor, sccProcessor :: (T id :<: f, DPMark f, Show id, Ord id) => ProblemG id f -> ProblemProofG id Html f
usableSCCsProcessor :: forall f id. (T LPId :<: f, DPMark f) => ProblemG LPId f -> ProblemProofG LPId Html f

usableSCCsProcessor problem@(Problem typ@GNarrowingModes{pi,goal} trs dps)
  | assert (isSoundAF pi problem) False = undefined
  | null cc   = success (UsableGraph gr reachable) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (UsableGraph gr reachable) problem
                 [return $ Problem typ trs (dpTRS (extractIxx dd ciclo) (restrictGt gr ciclo))
                      | ciclo <- cc, any (`Set.member` reachable) ciclo]
  where
   dd          = rulesArray dps
   gr          = getEDG problem
   cc          = filter isCycle (map Tree.flatten (G.scc gr))
   reachable   = Set.fromList (G.reachable gr =<< goal_pairs)
   goal_pairs  = [ i | (i,r) <- [0..] `zip` rules dps, Just f <- [rootSymbol (lhs r)], unmarkDPSymbol f `Set.member` AF.domain goal]
   isCycle [n] = n `elem` gr A.! n
   isCycle _   = True

usableSCCsProcessor p = sccProcessor p

sccProcessor problem@(Problem typ trs dps)
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (dpTRS (extractIxx dd ciclo) (restrictGt gr ciclo)) | ciclo <- cc]
    where dd = rulesArray dps
          gr = getEDG problem
          cc = filter isCycle (map Tree.flatten (G.scc gr))
          isCycle [n] = n `elem` gr A.! n
          isCycle _   = True

cycleProcessor problem@(Problem typ trs dps)
  | null cc   = success (DependencyGraph gr) problem
                (toHtml "We need to prove termination for all the cycles. There are no cycles, so the system is terminating")
  | otherwise =  andP (DependencyGraph gr) problem
                 [return $ Problem typ trs (dpTRS (extractIxx dd ciclo) (restrictGt gr ciclo)) | ciclo <- cc]
    where cc = cycles gr
          dd = rulesArray dps
          gr = getEDG problem

getEDG :: (Ord id, T id :<: f, DPMark f) => ProblemG id f -> G.Graph
getEDG (Problem typ trs (rules->dps)) | (isBNarrowing .|. isGNarrowing) typ =
    G.buildG (0, length dps - 1)
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain (In in_t) u | [t'] <- variant' [In(icap trs <$> in_t)] [u] = isJust (unify t' u)

getEDG (Problem typ trs (rules->dps)) =
    G.buildG (0, length dps - 1)
               [ (i,j) | (i,_:->t) <- zip [0..] dps
                       , (j,u:->_) <- zip [0..] dps
                       , inChain t u]
    where inChain (In in_t) u | [t'] <- variant' [ren $ In (icap trs <$> in_t)] [u] = isJust (unify u t')

extractIxx arr nodes = A.listArray (0, length nodes - 1) [arr A.! n | n <- nodes]
restrictGt gr nodes  = A.amap (catMaybes . map (`lookup` newIndexes)) (extractIxx gr nodes)
  where newIndexes = zip nodes [0..]

ren :: (Var :<: f, HashConsed f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

cap, icap :: forall trs f id. (Ord id, TRSC f, TRS trs id f) => trs -> Term f -> Term f
cap trs t = evalState (go t) freshvv where
  freshvv = map var [0..] \\ vars' t
  go (open -> Just (T (s::id) tt)) | isDefined trs t = next
                                   | otherwise       = term s <$> P.mapM go tt
  go v = return v

-- Use unification instead of just checking if it is a defined symbol
-- This is not the icap defined in Rene Thiemann. I.e. it does not integrate the REN function
icap trs t = runSupply (go t) where
  go t@(In in_t) | Just (T (f::id) tt) <- open t
                 , f `Set.member` getDefinedSymbols trs = do
      t' <- In <$> (go `T.mapM` in_t)
      if  any (unifies t' . lhs) (rules trs) then var <$> next else return t'
  go v = return v
