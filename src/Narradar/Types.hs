{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE TypeOperators, PatternSignatures #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs, TypeFamilies #-}


module Narradar.Types ( module TRS
                      , module Narradar.Types
                      , module Narradar.TRS
                      , module Narradar.DPIdentifiers
                      , module Narradar.PrologIdentifiers
                      , module Narradar.Labellings
                      , module Narradar.Convert
                      ) where

import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Control.Applicative (Applicative(..),(<$>),(<*>))
import Data.Foldable (Foldable(..), sum, toList)
import Data.Graph (Graph, Vertex)
import Data.HashTable (hashString)
import Data.Int
import Data.List ((\\), groupBy, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import Unsafe.Coerce
import Text.Printf
import Text.ParserCombinators.Parsec
import Text.Show
import Text.PrettyPrint ((<>), parens, punctuate, comma, text, sep, vcat, Doc)
import qualified Text.PrettyPrint as Ppr

import Control.Monad.Free
import Narradar.ArgumentFiltering (AF, AF_, ApplyAF(..), ApplyAF_rhs(..), init)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.TRS
import Narradar.Convert
import Narradar.Utils

import Lattice
import TRS hiding (apply)
import TRS.FetchRules
import TRS.Bottom as Bottom
import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.TypeChecker as Prolog
import qualified Language.Prolog.Parser as Prolog
import Prelude as P hiding (sum, pi, mapM)

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

class    ExtraVars t f | t -> f where extraVars :: t -> [Term f]

instance (Ord id, TRSC f, T id :<: f) => ExtraVars (ProblemG id f) f where
    {-# SPECIALIZE instance ExtraVars (Problem BBasicId) BBasicId #-}
    extraVars (Problem _ trs dps) = extraVars trs ++ extraVars dps
instance (Ord id, TRSC f, T id :<: f) => ExtraVars (NarradarTRS id f) f where
    {-# SPECIALIZE instance ExtraVars (NarradarTRS Id BBasicId) BBasicId #-}
    extraVars trs = concatMap extraVars (rules trs)
instance (Ord (Term f), IsVar f, Foldable f) => ExtraVars (Rule f) f where
    {-# SPECIALIZE instance ExtraVars (Rule BBasicId) BBasicId #-}
    extraVars (l:->r) = snub (vars' r \\ vars' l)

---------------------------
-- DP Problems
---------------------------
type DP a = Rule a
type ProblemType id = ProblemTypeF (AF_ id)
data ProblemF id a = Problem {typ::(ProblemType id), trs,dps::a}
     deriving (Eq,Show)

instance Size a => Size (ProblemF id a) where size = sum . fmap size
instance Ord id => HasSignature (ProblemG id f) id where
  {-# SPECIALIZE instance HasSignature (Problem BBasicId) Id #-}
  getSignature (Problem _ trs dps) = getSignature trs `mappend` getSignature dps
--  getSignature PrologProblem{} = error "getSignature: tried to get the signature of a PrologProblem"

type Problem     f = ProblemG Id f
type ProblemG id f = ProblemF id (NarradarTRS id f)

data ProblemTypeF pi   = Rewriting
                       | Narrowing   | NarrowingModes   {pi::pi, types::Maybe Prolog.TypeAssignment, goal::pi}
                       | GNarrowing  | GNarrowingModes  {pi::pi, types::Maybe Prolog.TypeAssignment, goal::pi}
                       | BNarrowing  | BNarrowingModes  {pi::pi, types::Maybe Prolog.TypeAssignment, goal::pi}
                       | LBNarrowing | LBNarrowingModes {pi::pi, types::Maybe Prolog.TypeAssignment, goal::pi}
	               | Prolog {goals::[AF_ String], program::Prolog.Program}
                    deriving (Eq, Show)

narrowingModes0 =   NarrowingModes  {types=Nothing, goal=error "narrowingModes0", pi=error "narrowingModes0"}
bnarrowingModes0 =  BNarrowingModes {types=Nothing, goal=error "bnarrowingModes0", pi=error "bnarrowingModes0"}
gnarrowingModes0 =  GNarrowingModes {types=Nothing, goal=error "gnarrowingModes0", pi=error "gnarrowingModes0"}
lbnarrowingModes0 = LBNarrowingModes{types=Nothing, goal=error "lbnarrowingModes0", pi=error "lbnarrowingModes0"}

mkProblem :: (Show id, Ord id) => ProblemType id -> NarradarTRS id f -> NarradarTRS id f -> ProblemG id f
mkProblem typ@(getGoalAF -> Just pi) trs dps = let p = Problem (typ `withGoalAF` AF.restrictTo p pi) trs dps in p
mkProblem typ trs dps = Problem typ trs dps

mkDPSig (getSignature -> sig@Sig{..}) | dd <- toList definedSymbols =
  sig{definedSymbols = definedSymbols `Set.union` Set.mapMonotonic markDPSymbol definedSymbols
     ,arity          = arity `Map.union` Map.fromList [(markDPSymbol f, getArity sig f) | f <- dd]
     }

instance (ConvertT f f', Convert id id', Ord id, Ord id', T id :<: f, T id' :<: f', TRSC f, TRSC f' ) => Convert (ProblemG id f) (ProblemG id' f') where
  convert p@Problem{..} = (fmap convert p){typ = fmap convert typ}
--  convert (PrologProblem typ gg cc) = PrologProblem (fmap convert typ) gg cc


data VoidF f; instance Functor VoidF; instance TRS.Ppr VoidF

type PrologProblem = ProblemG String Basic'
mkPrologProblem :: [AF_ String] -> Prolog.Program -> PrologProblem
mkPrologProblem gg pgm = mkProblem (Prolog gg pgm) mempty mempty

mkGoalAF (T f tt) = AF.singleton f [ i | (i,G) <- zip [1..] tt]

isProlog Prolog{} = True ; isProlog _ = False
--isPrologProblem PrologProblem{} = True
isPrologProblem = isProlog . typ

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

isGNarrowing GNarrowing{}  = True
isGNarrowing GNarrowingModes{} = True
isGNarrowing _ = False
isGNarrowingProblem = isGNarrowing . typ

isAnyNarrowing = isFullNarrowing .|. isBNarrowing .|. isGNarrowing
isAnyNarrowingProblem = isAnyNarrowing . typ

isRewriting Rewriting =True; isRewriting _ = False
isRewritingProblem = isRewriting . typ

isLeftStrategy LBNarrowingModes{} = True; isLeftStrategy _ = False

isModed = isJust . getGoalAF
isModedProblem = isModed . typ

getProblemAF = getGoalAF
getGoalAF NarrowingModes{pi}   = Just pi
getGoalAF BNarrowingModes{pi}  = Just pi
getGoalAF GNarrowingModes{pi}  = Just pi
getGoalAF LBNarrowingModes{pi} = Just pi
getGoalAF _ = Nothing

getTyping NarrowingModes{types}   = types
getTyping GNarrowingModes{types}  = types
getTyping BNarrowingModes{types}  = types
getTyping LBNarrowingModes{types} = types
getTyping _ = Nothing

-- -------------
-- AF Problems
-- -------------

class WithGoalAF t id where
  type T' t id :: *
  withGoalAF :: t -> AF_ id -> T' t id

instance (WithGoalAF (ProblemType id) id) => WithGoalAF (ProblemG id f) id where
  type T' (ProblemG id f) id = ProblemG id f
  withGoalAF(Problem typ trs dps) goal = Problem (withGoalAF typ goal) trs dps
{-
instance (Convert id id', Ord id', Show id) =>  WithGoalAF (ProblemType id) id' where
  type T' (ProblemType id) id' = ProblemType id'
  withGoalAF pt@NarrowingModes{..}   pi' = pt{pi=pi', goal = convert goal :: AF_ id'}
  withGoalAF pt@BNarrowingModes{..}  pi' = pt{pi=pi', goal = convert goal :: AF_ id'}
  withGoalAF pt@LBNarrowingModes{..} pi' = pt{pi=pi', goal = convert goal :: AF_ id'}
  withGoalAF Narrowing   pi = narrowingModes0{pi, goal=pi}
  withGoalAF BNarrowing  pi = bnarrowingModes0{pi,goal=pi}
  withGoalAF LBNarrowing pi = lbnarrowingModes0{pi,goal=pi}
  withGoalAF Rewriting   _  = Rewriting
--  withGoalAF typ@Prolog{} _ =
  withGoalAF typ _ = error ("withGoalAF - error: " ++ show typ)
-}
instance (Show id) =>  WithGoalAF (ProblemType id) id where
  type T' (ProblemType id) id = ProblemType id
  withGoalAF pt@NarrowingModes{..}   pi' = pt{pi=pi'}
  withGoalAF pt@BNarrowingModes{..}  pi' = pt{pi=pi'}
  withGoalAF pt@GNarrowingModes{..}  pi' = pt{pi=pi'}
  withGoalAF pt@LBNarrowingModes{..} pi' = pt{pi=pi'}
  withGoalAF Narrowing   pi = narrowingModes0{pi}
  withGoalAF BNarrowing  pi = bnarrowingModes0{pi}
  withGoalAF GNarrowing  pi = gnarrowingModes0{pi}
  withGoalAF LBNarrowing pi = lbnarrowingModes0{pi}
  withGoalAF Rewriting   _  = Rewriting
--  withGoalAF typ@Prolog{} _ =
  withGoalAF typ _ = error ("withGoalAF - error: " ++ show typ)

instance (Ord id) => ApplyAF (ProblemG id f) id where
    {-# SPECIALIZE instance ApplyAF (Problem BBasicId) Id #-}
    apply pi p@(Problem typ trs dps) = Problem typ (apply pi trs) (apply pi dps)

instance (Bottom.Bottom :<: f, Ord id, HasSignature sig id) => ApplyAF_rhs (ProblemG id f) sig id where
    apply_rhs _ pi p@(Problem typ trs dps) = Problem typ (apply_rhs p pi trs) (apply_rhs p pi dps)

-- ------------
-- Processors
-- ------------
data ProcInfo id where                    -- vv ignored vv
    GroundOne       :: Show id => Maybe (AF_ id) -> ProcInfo id
    GroundAll       :: Show id => Maybe (AF_ id) -> ProcInfo id
    EVProc          :: Show id => AF_ id -> ProcInfo id
    DependencyGraph :: Graph -> ProcInfo ()
    UsableGraph     :: Graph -> Set Vertex -> ProcInfo ()
    Polynomial      :: ProcInfo ()
    External        :: ExternalProc -> ProcInfo ()
    NarrowingP      :: ProcInfo ()
    InstantiationP  :: ProcInfo ()
    FInstantiationP :: ProcInfo ()
    PrologP         :: ProcInfo ()
    PrologSKP       :: ProcInfo ()
    LabellingSKP    :: [Labelled String] -> ProcInfo ()
    PrologSKP_rhs   :: ProcInfo ()
    LabellingSKP_rhs:: ProcInfo ()
    UsableRulesNaiveP :: ProcInfo ()
    UsableRulesP    :: ProcInfo ()
    Trivial         :: ProcInfo ()

isAFProc GroundOne{} = True
isAFProc GroundAll{} = True
isAFProc EVProc{}    = True
isAFProc GroundOne{} = True
isAFProc _           = False

instance Show id => Show (ProcInfo id) where
    show (DependencyGraph _) = "Dependency Graph Processor"
    show (UsableGraph _ _)= "Usable Graph Processor"
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
    show (LabellingSKP mm)= "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation + Labelling) \n" ++
                            "Modes used " ++ show (length mm) ++ ": " ++ (unlines $ map (unwords . map show) $ groupBy ((==) `on` unlabel) $ sort mm)
    show PrologSKP_rhs    = "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation + rhs bottoms trick)"
    show LabellingSKP_rhs = "Termination of LP as termination of Narrowing \n (Schneider-Kamp transformation + Labelling + rhs bottoms trick)"
    show UsableRulesP     = "Usable Rules for Basic Narrowing or Full Narrowing with constructor substitutions"
    show Trivial          = "Trivially non terminating"

--pprLabellingAsMode (Labelled f mm) = text f <> parens (hsep $ punctuate comma [ if | m <- mm])

data ExternalProc = MuTerm | Aprove String | Other String   deriving Eq
instance Show ExternalProc where
    show (Aprove msg) = "Aprove " ++ msg
    show (Other  msg) = msg
-- ------
-- Modes
-- ------
data Mode = G | V deriving (Eq, Bounded)
type Goal id = T id Mode
instance Show Mode where show G = "b"; show V = "f"

goalP =do
      spaces
      id <- Prolog.ident
      modes <- modesP
      return (AF.singleton id [i | (i,G) <- zip [1..] modes])

modesP = parens (modeP `sepBy` char ',') where parens= between (char '(') (char ')')
modeP = (oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V)

parseGoal :: String -> Either ParseError (AF_ String)
parseGoal = parse goalP ""

pprGoal :: (Goal String) -> Doc
pprGoal (T id modes) = text id <> parens(sep$ punctuate comma $ map (text.show) modes)

pprGoalAF :: (String ~ id, Ord id, Show id) => Signature id -> AF_ id -> Doc
pprGoalAF sig pi = vcat [ pprGoal (T f mm) | (f,pp) <- AF.toList pi
                                           , f `Set.member` allSymbols sig
                                           , let mm = [if i `elem` pp then G else V | i <- [1..getArity sig f] ]]

-- --------------------------
-- Parsing Prolog problems
-- --------------------------
data PrologSection = Query [Prolog.Atom] | Clause Prolog.Clause | QueryString String

problemParser = do
  txt <- getInput
  let !queryComments = map QueryString $ catMaybes $ map f (lines txt)
  res <- Prolog.whiteSpace >> many (Clause <$> Prolog.clause <|> Query <$> Prolog.query)
  return (res ++ queryComments)
  where f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
        f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
        f _ = Nothing

--mkPrologProblem = (return.) . mkPrologProblem
parsePrologProblem pgm = mapLeft show $ do
     things <- parse problemParser "input" pgm
     let cc      = [c | Clause      c <- things]
         gg1     = [q | Query       q <- things]
         gg_txt  = [q | QueryString q <- things]
     gg2    <- mapM parseGoal gg_txt
     gg1'   <- mapM atomToGoal (concat gg1)
     return (mkPrologProblem (gg1' ++ gg2) cc)
 where
     atomToGoal (Prolog.Pred f tt) = do
       mm <- parse modesP "" $ unwords $ map (show . Prolog.ppr) $ tt
       return (AF.singleton f [i | (i,G) <- zip [1..] mm])

-- ------------------
-- Functor Instances
-- ------------------

$(derive makeFunctor     ''ProblemF)
$(derive makeFoldable    ''ProblemF)
$(derive makeTraversable ''ProblemF)
$(derive makeFunctor     ''ProblemTypeF)
$(derive makeFoldable    ''ProblemTypeF)
$(derive makeTraversable ''ProblemTypeF)
