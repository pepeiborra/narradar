{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Narradar.Processor.SubtermCriterion where

import Control.Monad
import Control.Monad.Failure
import Data.List (insert, maximumBy, sort, sortBy)
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set

import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Types
import qualified Narradar.Types.Problem.InitialGoal as InitialGoal
import qualified Narradar.Types.Problem.NarrowingGen as NarrowingGen
import Narradar.Types.ArgumentFiltering (AF_)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Utils (on)

data SubtermCriterion         = SubtermCriterion deriving (Eq, Show, Ord)
data SubtermCriterionProof id = SubtermCriterionProof (Proj id)
                              | SubtermCriterionFailMinimality
     deriving (Eq, Show, Ord)

instance (Pretty (DPIdentifier id), Ord id) => Pretty (SubtermCriterionProof (DPIdentifier id)) where
    pPrint SubtermCriterionFailMinimality = text "The problem does not have the minimality property," $$
                                            text "nor is innermost, hence the subterm criterion does not apply"

    pPrint (SubtermCriterionProof pi) = text "Subterm Criterion with the projection:" $$
                                        nest 2 pi

instance (Info info (SubtermCriterionProof id), Ord id, Pretty id) =>
         Processor info SubtermCriterion (Problem Rewriting (NTRS id)) (Problem Rewriting (NTRS id))
  where
   apply SubtermCriterion p0
     | getMinimalityFromProblem p0 /= M = dontKnow (SubtermCriterionFailMinimality ::SubtermCriterionProof id) p0
     | otherwise = case subtermCriterion (getP p0) of
                                Nothing          -> mzero
                                Just (pTRS',prj) -> singleP (SubtermCriterionProof prj) p0 (setP pTRS' p0)

instance (Info info (SubtermCriterionProof id),Ord id, Pretty id) =>
         Processor info SubtermCriterion (Problem IRewriting (NTRS id)) (Problem IRewriting (NTRS id))
  where
   apply SubtermCriterion p0 = case subtermCriterion (getP p0) of
                                Nothing          -> mzero
                                Just (pTRS',prj) -> singleP  (SubtermCriterionProof prj) p0 (setP pTRS' p0)

instance(Info info (Problem base (NTRS id))
        ,Processor info SubtermCriterion (Problem base (NTRS id)) (Problem base (NTRS id))) =>
         Processor info SubtermCriterion (Problem (MkNarrowingGen base) (NTRS id)) (Problem (MkNarrowingGen base) (NTRS id))
  where
   apply = liftProcessor

instance (Info info (Problem base (NTRS id))
         ,Processor info SubtermCriterion (Problem base (NTRS id)) (Problem base (NTRS id))) =>
         Processor info SubtermCriterion (Problem (InitialGoal (TermF id) base) (NTRS id)) (Problem (InitialGoal (TermF id) base) (NTRS id))
  where
   apply = liftProcessor

-- --------------
-- Implementation
-- --------------

subtermCriterion :: Ord id => NTRS id -> Maybe (NTRS id, Proj id)
subtermCriterion pTRS
  | null prjs = Nothing
  | prj <- maximum prjs
  , nonStrictPrjs <- [ i | (i, dp) <- [0..] `zip` rules pTRS, isWeakOn dp prj]
  = Just (restrictTRS pTRS nonStrictPrjs, prj)
  where
    prjs = validPrjs pTRS

------------------------

data Kind = Weak | Strict deriving (Eq, Ord, Show)
data Proj id = Proj {af::AF_ id, kind::[Kind]} deriving Show

proj af kk = Proj af (sort kk)

-- | for performance, the second projection should be 'smaller' than the first one
combine (Proj af k) (Proj af' k')
--  | length k < length k' = do { af'' <- AF.combine af af'; return (Proj af'' (foldr insert k' k))}
  | otherwise            = do { af'' <- AF.combine af af'; return (Proj af'' (foldr insert k k'))}

isWeakOn (l:->r) (Proj af _) = AF.apply af l == AF.apply af r

instance Eq id => Eq (Proj id)   where Proj _ kk1 == Proj _ kk2 = kk1 == kk2
instance Ord id => Ord (Proj id) where compare (Proj _ kk1) (Proj _ kk2) = compare kk1 kk2
instance (Ord id, Pretty (DPIdentifier id)) => Pretty (Proj (DPIdentifier id)) where
    pPrint = pPrint . AF.filter (\id _ -> isDPSymbol id) . af

--------------------------------------

validPrjs pTRS = go (proj (AF.init dps) []) dps
 where
  sig = getSignature pTRS
  dps = rules pTRS

  go prj [] = return prj
  go prj (dp:rest) = do
    prj'  <- pairPrjs sig dp
    prj'' <- combine prj prj'
    go prj'' rest

pairPrjs :: Ord id => Signature id -> RuleN id -> [Proj id]
pairPrjs sig (l@(rootSymbol -> Just f) :-> r@(rootSymbol -> Just g))
 | f == g
 = do
    i <- [1 .. getArity sig f]
    let l_i = l ! [i]
        r_i = r ! [i]
        sub_l = Set.fromList (subterms l_i)

    guard (r_i `Set.member` sub_l)

    let af   = AF.fromList' [(f,Left i)]
        kind = if r_i == l_i then Weak else Strict

    return (proj af [kind])

 | otherwise
 = do
    i <- [1 .. getArity sig f]
    let l_i = l ! [i]
        sub_l = Set.fromList (subterms l_i)

    j <- [1 .. getArity sig g]
    let r_j = r ! [j]

    guard (r_j `Set.member` sub_l)

    let af   = AF.fromList' [(f,Left i), (g, Left j)]
        kind = if r_j == l_i then Weak else Strict

    return (proj af [kind])

pairPrjs _ _ = failure "pairPrjs: no projections"