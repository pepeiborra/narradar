{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Narradar.ExtraVars ( ExtraVars(..)
                          , evProcessor, invariantEV
                          , cutWith
                          , sortByDefinedness, selectBest, isSoundAF)
                       where

import Control.Applicative
import Control.Exception
import qualified Control.Monad as P
import Control.RMonad hiding (fmap,join)
import Control.Monad.Fix (fix)
import Control.Monad.Writer (Writer(..), MonadWriter(..))
import Data.Foldable (Foldable(..), toList)
import Data.List (find, sortBy, inits, unfoldr, isPrefixOf, isSuffixOf, intersect,(\\))
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Traversable (Traversable)
import Text.PrettyPrint
import Prelude hiding (Monad(..), (=<<), or, and, mapM, pi)
import qualified Prelude as P

import Lattice
import Narradar.ArgumentFiltering (AF, LabelledAF, AF_, Heuristic, bestHeu, typeHeu, mkHeu, Heuristic(..), MkHeu(..))
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Types
import Narradar.Proof
import Narradar.Utils(on,snub)
import Narradar.Term
import Narradar.Var

import Data.Term.Rules

trace _ = id

class    ExtraVars v thing | thing -> v where extraVars :: thing -> [v]
instance (Ord v, Ord (Term t v), Functor t, Foldable t, HasRules t v trs) => ExtraVars v trs where
    extraVars = concatMap extraVars . rules

instance (Ord v, Functor t, Ord (Term t v), Foldable t) => ExtraVars v (Rule t v) where
    extraVars (l:->r) = Set.toList (Set.fromList(vars r) `Set.difference` Set.fromList(vars l))

evProcessor _ p | not (isAnyNarrowingProblem p) = P.return p
evProcessor mkH p@(Problem typ@(getAF -> Just af) trs dps)
     | null extra      = P.return p
     | null orProblems = failP EVProcFail p
     | otherwise = P.msum (map P.return orProblems)
  where extra = extraVars p
        heu = mkHeu mkH p
        orProblems = [(p `withAF` af') | af' <- Set.toList $ invariantEV heu p af]

evProcessor mkH p@(Problem typ trs dps) = evProcessor mkH (p `withAF` AF.init p)
evProcessor _ p = P.return p

--cutWith :: (Ppr id, Ord id) => Heuristic id t -> AF_ id -> TermN id v -> [Position] -> Set.Set (AF_ id)
cutWith heu af t [] = return af
cutWith heu af t pp = foldM (\af' pos -> (runHeu heu af' t pos >>= \(f,p) ->
--                           trace ("term: " ++ show(ppr t) ++ ", pos: " ++ show pos ++ ", symbol:" ++ show (ppr f) ++ ", i: " ++ show p) $
                             return$ AF.cut f p af'))
                            af pp
--cutWith heu af t pp = mconcat `liftM` (mapM (heu af t >=> \(f,p) -> return$ AF.cut f p af) pp)

invariantEV :: ( Ppr id, Ord id, Lattice (AF_ id), HasRules (TermF id) Var trs
               , ExtraVars v trs, AF.ApplyAF trs id) =>
               AF.Heuristic id (TermF id) -> trs -> AF_ id -> Set (AF_ id)
invariantEV heu trs pi = let pi' = (selectBest . Set.toList . fix subinvariantEV) pi
                         in assert (all (`isSoundAF` trs) pi') (Set.fromList pi')
  where
        subinvariantEV f af
                | null extra = return af
                | otherwise  = foldM cutEV af (rules trs) >>= f
              where extra = extraVars (AF.apply af trs)
        cutEV af rule@(_:->r)
            | orig_poss <- noteV <$> extraVars (AF.apply af (annotateWithPos <$> rule))
            = cutWith heu af r orig_poss

sortByDefinedness :: (Ord id, Foldable trs, Size (trs a)) => (AF_ id -> trs a -> trs a) -> trs a -> [AF_ id] -> [AF_ id]
sortByDefinedness apply dps = sortBy (flip compare `on` dpsSize)
    where dpsSize af = size $ (apply af dps)

selectBest = unfoldr findOne where
          findOne [] = Nothing
          findOne (m:xx)
              | any (\x -> Just True == lt m x) xx = findOne xx
              | otherwise = Just (m, filter (uncomparableTo m) xx)
              where uncomparableTo x y = isNothing (lt x y)


-- ----------
-- Soundness
-- ----------
isSoundAF     af trs = null (extraVars $ AF.apply af trs)
