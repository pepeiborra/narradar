{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}

module Types (module TRS, module Types, module Identifiers) where

import Control.Applicative ((<$>),(<*>))
import Data.Foldable (Foldable(..), sum)
import Data.Graph (Graph)
import Data.HashTable (hashString)
import Data.Int
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable
import Unsafe.Coerce
import Text.Printf
import Text.ParserCombinators.Parsec
import Text.Show
import Text.PrettyPrint ((<>), parens, punctuate, comma, text, sep)
import qualified Text.PrettyPrint as Ppr

import TRS hiding (apply)
import ArgumentFiltering (AF, ApplyAF(..))
import Identifiers
import Lattice
import Control.Monad.Free
import Utils
import qualified Language.Prolog.Syntax as Prolog
import Prelude as P hiding (sum)

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

class    ExtraVars t f | t -> f where extraVars :: t -> [Term f]
instance ExtraVars (Problem f)f where extraVars (Problem _ trs@TRS{} dps) = extraVars trs ++ extraVars dps
instance ExtraVars (TRS id f) f where extraVars trs@TRS{} = concatMap extraVars (rules trs)
instance (Ord (Term f), IsVar f, Foldable f) => ExtraVars (Rule f) f where extraVars (l:->r) = snub (vars' r \\ vars' l)

---------------------------
-- DP Problems
---------------------------
type  DP a = Rule a

data Problem_ a = Problem       {typ::ProblemType, trs,dps::a}
                | PrologProblem {typ::ProblemType, goals::[Goal], program::Prolog.Program}
     deriving (Eq,Show)

instance Functor  Problem_ where fmap f (Problem typ a b) = Problem typ (f a) (f b)
instance Foldable Problem_ where foldMap f (Problem _ a b) = f a `mappend` f b
instance Traversable Problem_ where traverse f (Problem typ a b) = Problem typ <$> f a <*> f b
instance Size a => Size (Problem_ a) where size = sum . fmap size
instance SignatureC (Problem f) Identifier where
  getSignature (Problem _ trs@TRS{} dps@TRS{}) = sig trs `mappend` sig dps

type Problem f = Problem_ (TRS Identifier f)

data ProblemType = Rewriting
                 | Narrowing   | NarrowingModes AF
                 | BNarrowing  | BNarrowingModes AF
                 | LBNarrowing | LBNarrowingModes AF
		 | Prolog
                   deriving (Eq, Show)

prologProblem = PrologProblem Prolog
isProlog Prolog = True ; isProlog _ = False
isPrologProblem PrologProblem{} = True
isPrologProblem p = isProlog $ typ p

isFullNarrowing Narrowing{} = True
isFullNarrowing NarrowingModes{} = True
isFullNarrowing _ = False
isFullNarrowingProblem = isFullNarrowing . typ

isBNarrowing BNarrowing{}  = True
isBNarrowing LBNarrowing{} = True
isBNarrowing BNarrowingModes{} = True
isBNarrowing LBNarrowingModes{} = True
isBNarrowing _ = False
isBNarrowingProblem = isBNarrowing . typ

isAnyNarrowing p = isFullNarrowing p || isBNarrowing p
isAnyNarrowingProblem = isAnyNarrowing . typ

isRewriting Rewriting =True; isRewriting _ = False
isRewritingProblem = isRewriting . typ

isLeftStrategy LBNarrowingModes{} = True; isLeftStrategy _ = False

isModed = isJust . getGoalAF
isModedProblem = isModed . typ

getGoalAF (NarrowingModes goal) = Just goal
getGoalAF (BNarrowingModes goal) = Just goal
getGoalAF (LBNarrowingModes goal) = Just goal
getGoalAF _ = Nothing

withGoalAF(Problem Narrowing trs dps)   goal = Problem (NarrowingModes goal) trs dps
withGoalAF(Problem BNarrowing trs dps)  goal = Problem (BNarrowingModes goal) trs dps
withGoalAF(Problem LBNarrowing trs dps) goal = Problem (LBNarrowingModes goal) trs dps

data Mode = G | V deriving (Show, Eq, Bounded)
type Goal = T String Mode

instance ApplyAF (Problem f) where
    apply af p@(Problem typ trs@TRS{} dps) = Problem typ (apply af trs) (apply af dps)


-- ------------
-- Processors
-- ------------
data ProcInfo = AFProc (Maybe AF) (Maybe (Division Identifier))
              | DependencyGraph Graph
              | Polynomial
              | External ExternalProc
              | NarrowingP
              | InstantiationP
              | FInstantiationP
              | PrologP
              | PrologSKP

instance Show ProcInfo where
    show (DependencyGraph _) = "Dependency Graph Processor"
    show (External proc) = "External: " ++ show proc
    show NarrowingP      = "Narrowing"
    show InstantiationP  = "Instantiation"
    show FInstantiationP  = "Forward Instantiation"
    show (AFProc (Just af) Nothing) = show af
    show (AFProc (Just af) (Just div)) = show af ++ showParen True (shows (Map.toList div)) ""
    show (AFProc Nothing _) = "Argument Filtering"
    show (Polynomial)    = "Polynomial ordering"
    show PrologP          = "Termination of LP as termination of Leftmost Basic Narrowing"
    show PrologSKP        = "Termination of LP as termination of Leftmost Basic Narrowing \n (Schneider-Kamp transformation)"

data ExternalProc = MuTerm | Aprove | Other String
     deriving (Eq, Show)

-- ------
-- Modes
-- ------
type Division id = Map id [Mode]
type DivEnv      = Map Int Mode

instance Lattice Mode where
    join G G = G
    join _ _ = V
    meet V V = V
    meet _ _ = G
    top      = V
    bottom   = G

instance Lattice [Mode] where
    meet     = P.zipWith meet
    join     = P.zipWith Lattice.join
    top      = repeat top
    bottom   = repeat bottom

instance Ord id => Lattice (Division id) where
    meet   = Map.unionWith meet
    join   = Map.unionWith  join
    bottom = Map.empty
    top    = Map.empty

instance Lattice DivEnv where
    meet   = Map.unionWith meet
    join   = Map.unionWith  join
    bottom = Map.empty
    top    = Map.empty

parseGoal :: String -> Either ParseError Goal
parseGoal = parse p "" where
    ident = many1 (alphaNum <|> oneOf "!+_-./<>=?\\/^")
    mode  = (oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V)
    parens= between (char '(') (char ')')
    p = do
      spaces
      id <- ident
      modes <- parens (mode `sepBy` char ',')
      return (T id modes)

pprGoal :: Goal -> String
pprGoal (T id modes) = show (text id <> parens(sep$ punctuate comma $ map (text.show) modes))