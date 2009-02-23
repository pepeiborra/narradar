{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs, TypeFamilies #-}

module Types (module TRS, module Types, module Identifiers, module Bottom) where

import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Control.Applicative (Applicative(..),(<$>),(<*>))
import Data.Foldable (Foldable(..), sum, toList)
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
import ArgumentFiltering (AF, AF_, ApplyAF(..), ApplyAF_rhs(..), init)
import Bottom
import Identifiers
import Lattice
import Control.Monad.Free
import Utils
import qualified Language.Prolog.Syntax as Prolog
import qualified Language.Prolog.TypeChecker as Prolog
import Prelude as P hiding (sum)

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

class    ExtraVars t f | t -> f where extraVars :: t -> [Term f]

instance (Ord id, DPMark f id) => ExtraVars (ProblemG id f) f where
    {-# SPECIALIZE instance ExtraVars (Problem BBasicId) BBasicId #-}
    extraVars (Problem _ trs dps) = extraVars trs ++ extraVars dps
instance (Ord id, DPMark f id) => ExtraVars (NarradarTRS id f) f where
    {-# SPECIALIZE instance ExtraVars (NarradarTRS Id BBasicId) BBasicId #-}
    extraVars trs = concatMap extraVars (rules trs)
instance (Ord (Term f), IsVar f, Foldable f) => ExtraVars (Rule f) f where
    {-# SPECIALIZE instance ExtraVars (Rule BBasicId) BBasicId #-}
    extraVars (l:->r) = snub (vars' r \\ vars' l)

---------------------------
-- DP Problems
---------------------------
type  DP a = Rule a

data ProblemF id a = Problem       {typ::(ProblemType id), trs,dps::a}
                   | PrologProblem {typ::(ProblemType id), goals::[Goal], program::Prolog.Program}
     deriving (Eq,Show)
{-
instance Functor  (ProblemF id) where fmap f (Problem typ a b) = Problem typ (f a) (f b)
instance Foldable ProblemF whee foldMap f (Problem _ a b) = f a `mappend` f b
instance Traversable ProblemF where traverse f (Problem typ a b) = Problem typ <$> f a <*> f b
-}

instance Size a => Size (ProblemF id a) where size = sum . fmap size
instance Ord id => SignatureC (ProblemG id f) id where
  {-# SPECIALIZE instance SignatureC (Problem BBasicId) Id #-}
  getSignature (Problem _ trs dps) = getSignature trs `mappend` getSignature dps
  getSignature PrologProblem{} = error "getSignature: tried to get the signature of a PrologProblem"

type Problem     f = ProblemG Identifier f
type ProblemG id f = ProblemF id (NarradarTRS id f)

data ProblemTypeF a = Rewriting
                    | Narrowing   | NarrowingModes   a (Maybe Prolog.TypeAssignment)
                    | BNarrowing  | BNarrowingModes  a (Maybe Prolog.TypeAssignment)
                    | LBNarrowing | LBNarrowingModes a (Maybe Prolog.TypeAssignment)
	            | Prolog
                    deriving (Eq, Show)


mkProblem :: ProblemType id -> NarradarTRS id f -> NarradarTRS id f -> ProblemG id f
mkProblem = Problem

mkDPSig (getSignature -> sig@Sig{..}) | dd <- toList definedSymbols =
  sig{definedSymbols = definedSymbols `Set.union` Set.mapMonotonic markDPSymbol definedSymbols
     ,arity          = arity `Map.union` Map.fromList [(markDPSymbol f, getArity sig f) | f <- dd]
     }

instance (ConvertT f f', Convert id id', Ord id, Ord id', T id :<: f, DPMark f' id', TRSC f, TRSC f' ) => Convert (ProblemG id f) (ProblemG id' f') where
  {-# SPECIALIZE instance Convert (Problem BBasicId) (ProblemG LId BBasicLId) #-}
  {-# SPECIALIZE instance Convert (ProblemG String Basic) (Problem BBasicId) #-}
  {-# SPECIALIZE instance Convert (ProblemG String Basic) (ProblemG LId BBasicLId) #-}
  convert p@Problem{..} = (fmap convert p){typ = fmap convert typ}
  convert (PrologProblem typ gg cc) = PrologProblem (fmap convert typ) gg cc

--mkPrologProblem :: [Goal] -> Prolog.Program -> ProblemG Identifier BBasicId
mkPrologProblem = PrologProblem Prolog

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

getGoalAF (NarrowingModes   goal _) = Just goal
getGoalAF (BNarrowingModes  goal _) = Just goal
getGoalAF (LBNarrowingModes goal _) = Just goal
getGoalAF _ = Nothing

getTyping (NarrowingModes   _ (Just a)) = Just a
getTyping (BNarrowingModes  _ (Just a)) = Just a
getTyping (LBNarrowingModes _ (Just a)) = Just a
getTyping _ = Nothing

getProblemAF = getGoalAF

-- -------------
-- AF Problems
-- -------------

type ProblemType id = ProblemTypeF (AF_ id)

class WithGoalAF t id where
  type T' t id :: *
  withGoalAF :: t -> AF_ id -> T' t id

class WithTyping t where
  withTyping :: t -> Prolog.TypeAssignment -> t

instance (WithGoalAF (ProblemType id) id) => WithGoalAF (ProblemG id f) id where
  type T' (ProblemG id f) id = ProblemG id f
  withGoalAF(Problem typ trs dps) goal = Problem (withGoalAF typ goal) trs dps

instance Show id =>  WithGoalAF (ProblemType id) id' where
  type T' (ProblemType id) id' = ProblemType id'
  withGoalAF (NarrowingModes   _ typ) pi' = NarrowingModes   pi' typ
  withGoalAF (BNarrowingModes  _ typ) pi' = BNarrowingModes  pi' typ
  withGoalAF (LBNarrowingModes _ typ) pi' = LBNarrowingModes pi' typ
  withGoalAF Narrowing   pi = NarrowingModes   pi Nothing
  withGoalAF BNarrowing  pi = BNarrowingModes  pi Nothing
  withGoalAF LBNarrowing pi = LBNarrowingModes pi Nothing
  withGoalAF Rewriting   _  = Rewriting
  withGoalAF Prolog      _  = Prolog
  withGoalAF typ _ = error ("withGoalAF - error: " ++ show typ)


instance WithTyping (ProblemType id) => WithTyping (ProblemG id f) where
  withTyping(Problem typ trs dps) goal = Problem (withTyping typ goal) trs dps

instance WithTyping (ProblemType id) where
  withTyping (NarrowingModes   pi _) typ' = NarrowingModes   pi (Just typ')
  withTyping (BNarrowingModes  pi _) typ' = BNarrowingModes  pi (Just typ')
  withTyping (LBNarrowingModes pi _) typ' = LBNarrowingModes pi (Just typ')
  withTyping Narrowing   typ = NarrowingModes   (error "Error: withTyping applied to a non AF problem type") (Just typ)
  withTyping BNarrowing  typ = BNarrowingModes  (error "Error: withTyping applied to a non AF problem type") (Just typ)
  withTyping LBNarrowing typ = LBNarrowingModes (error "Error: withTyping applied to a non AF problem type") (Just typ)
  withTyping Rewriting   _  = Rewriting
  withTyping Prolog      _  = Prolog
--  withTyping typ _ = error ("withTyping - error: " ++ show typ)


data Mode = G | V deriving (Show, Eq, Bounded)
type Goal = T String Mode

instance (Bottom.Bottom :<: f, Ord id) => ApplyAF (ProblemG id f) id where
    {-# SPECIALIZE instance ApplyAF (Problem BBasicId) Id #-}
    apply pi p@(Problem typ trs dps) = Problem typ (apply pi trs) (apply pi dps)

instance (Bottom.Bottom :<: f, Ord id, SignatureC sig id) => ApplyAF_rhs (ProblemG id f) sig id where
    apply_rhs _ pi p@(Problem typ trs dps) = Problem typ (apply_rhs p pi trs) (apply_rhs p pi dps)

-- ------------
-- Processors
-- ------------
data ProcInfo id where                    -- vv ignored vv
    GroundOne       :: Show id => Maybe (AF_ id) -> ProcInfo id
    GroundAll       :: Show id => Maybe (AF_ id) -> ProcInfo id
    EVProc          :: Show id => AF_ id -> ProcInfo id
    DependencyGraph :: Graph -> ProcInfo ()
    Polynomial      :: ProcInfo ()
    External        :: ExternalProc -> ProcInfo ()
    NarrowingP      :: ProcInfo ()
    InstantiationP  :: ProcInfo ()
    FInstantiationP :: ProcInfo ()
    PrologP         :: ProcInfo ()
    PrologSKP       :: ProcInfo ()
    LabellingSKP    :: ProcInfo ()
    PrologSKP_rhs   :: ProcInfo ()
    LabellingSKP_rhs:: ProcInfo ()
    UsableRulesP    :: ProcInfo ()
    Trivial         :: ProcInfo ()

isAFProc GroundOne{} = True
isAFProc GroundAll{} = True
isAFProc EVProc{}    = True
isAFProc GroundOne{} = True
isAFProc _           = False

instance Show id => Show (ProcInfo id) where
    show (DependencyGraph _) = "Dependency Graph Processor"
    show (External proc)  = "External: " ++ show proc
    show NarrowingP       = "Narrowing"
    show InstantiationP   = "Instantiation"
    show FInstantiationP  = "Forward Instantiation"
    show (GroundOne (Just pi)) = "ICLP08 AF Processor\n" ++ show pi
    show (GroundAll (Just pi)) = "All Rhs's Ground AF Processor\n" ++ show pi
    show (EVProc pi)      = "Eliminate Extra Vars \n" ++ show pi
    show (isAFProc -> True) = "Argument Filtering"
    show (Polynomial)     = "Polynomial ordering"
    show PrologP          = "Termination of LP as termination of Narrowing"
    show PrologSKP        = "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation)"
    show LabellingSKP     = "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation + Labelling)"
    show PrologSKP_rhs    = "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation + rhs bottoms trick)"
    show LabellingSKP_rhs = "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation + Labelling + rhs bottoms trick)"
    show UsableRulesP     = "Usable Rules for Basic Narrowing or Full Narrowing with constructor substitutions"
    show Trivial          = "Trivially non terminating"

data ExternalProc = MuTerm | Aprove String | Other String
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
    bottom   = repeat Lattice.bottom

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

-- ------------------
-- Functor Instances
-- ------------------

$(derive makeFunctor     ''ProblemF)
$(derive makeFoldable    ''ProblemF)
$(derive makeTraversable ''ProblemF)
$(derive makeFunctor     ''ProblemTypeF)
$(derive makeFoldable    ''ProblemTypeF)
$(derive makeTraversable ''ProblemTypeF)
