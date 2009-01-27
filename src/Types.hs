{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}

module Types (module TRS, module Types) where

import Control.Applicative ((<$>),(<*>))
import Data.Foldable (Foldable(..), sum)
import Data.Graph.Inductive.PatriciaTree
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
import TRS hiding (Basic)
import Text.Printf
import Text.ParserCombinators.Parsec
import Text.Show

import qualified ArgumentFiltering as AF
import Lattice
import Control.Monad.Free
import Utils
import Prelude as P hiding (sum)

type Basic   = Var :+: T String     :+: Hole
type BasicId = Var :+: T Identifier :+: Hole
instance HashConsed Basic
instance HashConsed BasicId
instance HashConsed (T Identifier)

data Identifier = IdFunction String | IdDP String | AnyIdentifier deriving (Ord)
instance Eq Identifier where
    IdFunction f1 == IdFunction f2 = f1 == f2
    IdDP f1       == IdDP f2       = f1 == f2
    AnyIdentifier == _             = True
    _             == AnyIdentifier = True
    _             == _             = False

instance Show Identifier where
    show (IdFunction f) = f
    show (IdDP n) = n ++ "#"

mkTRS :: [Rule Basic] -> TRS Identifier BasicId
mkTRS rr = TRS (Set.fromList rules') (getSignature rules') where rules' = fmap2 (foldTerm mkTIdF) rr

class (Functor f, Functor g) => MkTId f g where mkTIdF :: f (Term g) -> Term g
instance (T Identifier :<: g, HashConsed g) => MkTId (T String) g where mkTIdF (T f tt) = term (IdFunction f) tt
instance (MkTId f1 g, MkTId f2 g) => MkTId (f1 :+: f2) g where
    mkTIdF (Inl x) = mkTIdF x
    mkTIdF (Inr x) = mkTIdF x
instance (a :<: g, HashConsed g) => MkTId a g where mkTIdF t = inject(fmap reinject t)

{-
mkTRS rules = TRS rules' (getSignature rules') where
  rules' = fmap2 (foldTerm f) rules
--  f :: (T String :<: tstring, HashConsed tident, T Identifier :<: tident) => tstring (Term tident) -> Term tident
  f t
     | Just(T f tt) <- prj t = term (IdFunction f) tt
     | otherwise = fmap reinject t -- (unsafeCoerce t :: tident(Term tident))
-}

markDPSymbol (IdFunction f) = IdDP f
markDPSymbol f = f
unmarkDPSymbol (IdDP n) = IdFunction n
unmarkDPSymbol n = n

markDP, unmarkDP :: (HashConsed f, T Identifier :<: f) => Term f -> Term f
markDP t | Just (T (n::Identifier) tt) <- open t = term (markDPSymbol n) tt
         | otherwise                = t
unmarkDP t | Just (T (n::Identifier) tt) <- open t = term (unmarkDPSymbol n) tt
           | otherwise              = t

unmarkDPRule, markDPRule :: (HashConsed f,T Identifier :<: f) => Rule f -> Rule f
markDPRule   = fmap   markDP
unmarkDPRule = fmap unmarkDP

hashId :: Identifier -> Int32
hashId = hashString . show

instance HashTerm (T Identifier) where hashF (T id tt) = 14 * sum tt * hashId id

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

data Problem_ a = Problem {typ::ProblemType, trs,dps::a}
     deriving (Eq,Show)
instance Functor  Problem_ where fmap f (Problem typ a b) = Problem typ (f a) (f b)
instance Foldable Problem_ where foldMap f (Problem _ a b) = f a `mappend` f b
instance Traversable Problem_ where traverse f (Problem typ a b) = Problem typ <$> f a <*> f b
instance Size a => Size (Problem_ a) where size = sum . fmap size

type Problem f = Problem_ (TRS Identifier f)

data ProblemType = Rewriting
                 | Narrowing  | NarrowingModes Goal
                 | BNarrowing | BNarrowingModes Goal | LBNarrowingModes Goal
                 | Prolog Goal
     deriving (Eq, Show)

isFullNarrowing Narrowing{} = True
isFullNarrowing NarrowingModes{} = True
isFullNarrowing _ = False
isFullNarrowingProblem = isFullNarrowing . typ

isBNarrowing BNarrowing{} = True
isBNarrowing BNarrowingModes{} = True
isBNarrowing LBNarrowingModes{} = True
isBNarrowing _ = False
isBNarrowingProblem = isBNarrowing . typ

isAnyNarrowing p = isFullNarrowing p || isBNarrowing p
isAnyNarrowingProblem = isAnyNarrowing . typ

isRewriting Rewriting =True
isRewriting _ = False
isRewritingProblem = isRewriting . typ

isLeftStrategy LBNarrowingModes{} = True
isLeftStrategy _ = False

getGoal (NarrowingModes goal) = Just goal
getGoal (BNarrowingModes goal) = Just goal
getGoal (LBNarrowingModes goal) = Just goal
getGoal _ = Nothing

data Mode = G | V deriving (Show, Eq, Bounded)
type Goal = T String Mode

instance SignatureC (Problem f) Identifier where
  getSignature (Problem _ trs@TRS{} dps@TRS{}) = sig trs `mappend` sig dps

-- ------------
-- Processors
-- ------------
data ProcInfo = AFProc (Maybe AF.AF) (Maybe (Division Identifier))
              | DependencyGraph UGr
              | Polynomial
              | External ExternalProc
              | NarrowingP
              | InstantiationP
              | FInstantiationP

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

parseGoal :: String -> Either ParseError Goal
parseGoal = parse p "" where
    ident = many1 (alphaNum <|> oneOf "!+-./<>=?\\/^")
    mode  = (oneOf "g" >> return G) <|> (oneOf "v" >> return V)
    parens= between (char '(') (char ')')
    p = do
      spaces
      id <- ident
      modes <- parens (mode `sepBy` char ',')
      return (T id modes)