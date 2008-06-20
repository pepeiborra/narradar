{-# LANGUAGE PatternGuards, OverlappingInstances, UndecidableInstances, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module Problem where

import Control.Applicative
import Control.Monad (join)
import Data.AlaCarte
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Derive.Uniplate
import Data.Foldable as T
import Data.Maybe
import Data.Traversable as T
import Data.Generics.Uniplate
import Terms
import Text.PrettyPrint
import System.IO.Unsafe

import Types hiding (Ppr(..),ppr)
import qualified Types as TRS
import Utils
import qualified ArgumentFiltering as AF

import Prelude as P hiding (log, mapM, foldr, concatMap)

data Problem_ a = Problem  ProblemType a a
     deriving (Eq,Show)

type Problem a = Problem_ [Rule a]

data Progress_ f s a =   NotDone    a
                       | And        {procInfo::ProcInfo, problem::Problem f, subProblems::[Progress_ f s a]}
                       | Or         {procInfo::ProcInfo, problem::Problem f, subProblems::[Progress_ f s a]}
                       | Success    {procInfo::ProcInfo, problem::Problem f, res::s}
                       | Fail       {procInfo::ProcInfo, problem::Problem f, res::s}
                       | Empty
     deriving (Show)

type ProblemProgress s a = Progress_ a s (Problem a)

data ProcInfo = NarrowingAF
              | AFProc AF.AF
              | DependencyGraph
              | Polynomial
              | External ExternalProc
     deriving (Eq, Show)

data ExternalProc = MuTerm | Aprove | Other String
     deriving (Eq, Show)

data ProblemType = Rewriting | Narrowing
     deriving (Eq, Show)

instance Foldable Problem_ where foldMap = foldMapDefault
$(derive makeFunctor     ''Problem_)
$(derive makeTraversable ''Problem_)

instance Foldable (Progress_ f s) where foldMap = foldMapDefault
$(derive makeFunctor     ''Progress_)
$(derive makeTraversable ''Progress_)
-- $(derive makeUniplate    ''Progress_)

instance Monad (Progress_ f s) where
    return   = NotDone
    xs >>= f = join (fmap f xs)
      where join (NotDone p)    = p
            join (And pi pr pp) = And pi pr (map join pp)
            join (Or  pi pr pp) = Or  pi pr (map join pp)

success NotDone{} = False
success Success{} = True
success Fail{}    = False
success (And _ _ ll)  = P.all success ll
success (Or  _ _ ll)  = P.any success ll
success Empty     = True

solveProblem :: (Problem a -> ProblemProgress s a) -> ProblemProgress s a -> ProblemProgress s a
solveProblem = (=<<)

class Monad m => SolveProblemM m where
  solveProblemM :: (Problem a -> m (ProblemProgress s a)) -> ProblemProgress s a -> m (ProblemProgress s a)
  solveProblemM = concatMapM

instance SolveProblemM IO
{-
instance SolveProblemM IO where
  solveProblemM f p@Or{} = concatMap (unsafeInterleaveIO . f) p  -- This is sloppy but it suffices for the shape of our problems
  solveProblemM f p      =
    g (NotDone p) = f p
    g p@Or{}      = fmap join . traverse (unsafeInterleaveIO . f) p
    g x           = return x
-}

logLegacy proc prob Nothing = Fail proc prob "Failed"
logLegacy proc prob (Just msg) = Success proc prob msg

simplify p@(Or pi pb aa) | success p = listToMaybe [p | p <- aa, success p]
simplify p = Nothing


{-
class Loggable a where logProgress :: ProblemProgress -> a -> ProblemProgress
instance Loggable (ProblemProgress) where
    logProgress p' _p = p'
instance Loggable (Maybe String) where
  logProgress p Nothing    = Fail (procInfo p) (problem p) "failed"
  logProgress p (Just txt) = Success (procInfo p) (problem p) txt
--  logProgress
-}
{-
logResult :: Loggable a => Processor -> Problem -> Maybe a -> Log
logResult proc prob Nothing    = Fail proc prob (log "failed")
logResult proc prob (Just res) = Success proc prob (log res)
-}

class Ppr a where ppr :: a -> Doc

instance (Functor f, Foldable f, Ppr x) => Ppr (f x) where ppr = brackets . vcat . punctuate comma . toList . fmap ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance Show (Term a) => Ppr (Rule a) where ppr = text . show

instance Ppr ProblemType where
    ppr Narrowing = text "NDP"
    ppr Rewriting = text "DP"

instance Show (Term a) => Ppr (Problem a) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> (vcat $ map (text.show) dps)


instance TRS.Ppr a => Ppr (ProblemProgress String a) where
    ppr (NotDone prob) = ppr prob $$
                         text ("RESULT: Not solved yet")
    ppr (Success proc prob res) = ppr prob $$
                                  text "PROCESSOR: " <> text (show proc) $$
                                  text ("RESULT: Problem solved succesfully") $$
                                  text ("Output: ") <>  (vcat . map text . lines) res
    ppr (Fail proc prob res) = ppr prob $$
                               text "PROCESSOR: " <> (text.show) proc  $$
                               text ("RESULT: Problem could not be solved.") $$
                               text ("Output: ") <> (vcat . map text . lines) res
    ppr p@(Or proc prob sub) | Just res <- simplify p = ppr res
                  | otherwise =
                     ppr prob $$
                     text "PROCESSOR: " <> (text.show) proc $$
                     text ("Problem was translated to " ++ show (length sub) ++ " equivalent problems.") $$
                     nest 8 (vcat $ punctuate (text "\n") (map ppr sub))
    ppr (And proc prob sub)
        | length sub > 1=
                     ppr prob $$
                     text "PROCESSOR: " <> (text.show) proc $$
                     text ("Problem was divided to " ++ show (length sub) ++ " subproblems.") $$
                     nest 8 (vcat $ punctuate (text "\n") (map ppr sub))
        | otherwise =
                     ppr prob $$
                     text "PROCESSOR: " <> (text.show) proc $$
                     nest 8 (vcat $ punctuate (text "\n") (map ppr sub))


