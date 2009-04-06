{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs, TypeFamilies #-}


module Narradar.Types ( module TRS
                      , module Narradar.Types
                      , module Narradar.TRS
                      , module Narradar.ProblemType
                      , module Narradar.DPIdentifiers
                      , module Narradar.PrologIdentifiers
                      , module Narradar.Labellings
                      , module Narradar.Convert
                      , module Narradar.Unify
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
import Data.Traversable as T
import Unsafe.Coerce
import Text.Printf
import Text.ParserCombinators.Parsec
import Text.Show
import Text.PrettyPrint hiding (char, Mode)
import qualified Text.PrettyPrint as Ppr
import Control.Monad.State hiding (mapM)
import Prelude as P hiding (mapM, pi, sum)

import Control.Monad.Supply
import Control.Monad.Free
import Narradar.ArgumentFiltering (AF, AF_, ApplyAF(..), init)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.ProblemType
import Narradar.TRS
import Narradar.Convert
import Narradar.Utils
import Narradar.Unify

import Lattice
import TRS hiding (ppr, Ppr, apply, unify, unifies)
import qualified TRS
import TRS.FetchRules
import TRS.Bottom as Bottom
import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.TypeChecker as Prolog
import qualified Language.Prolog.Parser as Prolog
import Prelude as P hiding (sum, pi, mapM)

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

---------------------------
-- DP Problems
---------------------------
data ProblemF id a = Problem {typ::(ProblemType id), trs::a ,dps :: !a}
     deriving (Eq,Show)

instance Size a => Size (ProblemF id a) where size = sum . fmap size
instance Ord id => HasSignature (ProblemG id f) id where
  {-# SPECIALIZE instance HasSignature (Problem BBasicId) Id #-}
  getSignature (Problem _ trs dps) = getSignature trs `mappend` getSignature dps
--  getSignature PrologProblem{} = error "getSignature: tried to get the signature of a PrologProblem"

type Problem     f = ProblemG Id f
type ProblemG id f = ProblemF id (NarradarTRS id f)

instance (Ord (Term f), TRSC f, Ord id, T id :<: f) => Monoid (ProblemG id f) where
    mempty = Problem Rewriting mempty mempty
    Problem typ1 t1 dp1 `mappend` Problem typ2 t2 dp2 = Problem typ2 (t1 `mappend` t2) (dp1`mappend`dp2)

instance (Ord id, TRSC f, T id :<: f) => TRS (ProblemG id f) id f where
    rules (Problem _ trs dps) = rules trs `mappend` rules dps

mkProblem :: (Show id, Ord id) => ProblemType id -> NarradarTRS id f -> NarradarTRS id f -> ProblemG id f
mkProblem typ@(getGoalAF -> Just pi) trs dps = let p = Problem (typ `withGoalAF` AF.restrictTo (getAllSymbols p) pi) trs dps in p
mkProblem typ trs dps = Problem typ trs dps

mkDPSig (getSignature -> sig@Sig{..}) | dd <- toList definedSymbols =
  sig{definedSymbols = definedSymbols `Set.union` Set.mapMonotonic markDPSymbol definedSymbols
     ,arity          = arity `Map.union` Map.fromList [(markDPSymbol f, getArity sig f) | f <- dd]
     }

instance (ConvertT f f', Convert id id', Ord id, Ord id', T id :<: f, T id' :<: f', TRSC f, TRSC f' ) => Convert (ProblemG id f) (ProblemG id' f') where
  convert p@Problem{..} = (fmap convert p){typ = fmap convert typ}
--  convert (PrologProblem typ gg cc) = PrologProblem (fmap convert typ) gg cc

instance TRS.Ppr f => Ppr (ProblemG id f) where
    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps

--data VoidF f; instance Functor VoidF; instance TRS.Ppr VoidF

type PrologProblem = ProblemG String Basic'
mkPrologProblem :: [AF_ String] -> Prolog.Program -> PrologProblem
mkPrologProblem gg pgm = mkProblem (Prolog gg pgm) mempty mempty

mkGoalAF (T f tt) = AF.singleton f [ i | (i,G) <- zip [1..] tt]

isProlog Prolog{} = True ; isProlog _ = False
--isPrologProblem PrologProblem{} = True
isPrologProblem = isProlog . typ

isFullNarrowingProblem = isFullNarrowing . typ
isBNarrowingProblem    = isBNarrowing . typ
isGNarrowingProblem    = isGNarrowing . typ
isAnyNarrowingProblem  = isAnyNarrowing . typ
isRewritingProblem     = isRewriting . typ
--isModedProblem         = isModed . typ

getProblemAF = getGoalAF
getGoalAF NarrowingModes{pi}   = Just pi
getGoalAF BNarrowingModes{pi}  = Just pi
getGoalAF GNarrowingModes{pi}  = Just pi
getGoalAF LBNarrowingModes{pi} = Just pi
getGoalAF _ = Nothing

-- -------------
-- AF Problems
-- -------------

class WithGoalAF t id where
  type T' t id :: *
  withGoalAF :: t -> AF_ id -> T' t id

instance (WithGoalAF (ProblemType id) id) => WithGoalAF (ProblemG id f) id where
  type T' (ProblemG id f) id = ProblemG id f
  withGoalAF(Problem typ trs dps) goal = Problem (withGoalAF typ goal) trs dps

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

-- ------------
-- Processors
-- ------------
data ProcInfo id where                    -- vv ignored vv
    GroundOne       :: Show id => Maybe (AF_ id) -> ProcInfo id
    GroundAll       :: Show id => Maybe (AF_ id) -> ProcInfo id
    SafeAFP         :: Show id => Maybe (AF_ id) -> ProcInfo id
    EVProc          :: Show id => AF_ id -> ProcInfo id
    DependencyGraph :: Graph -> ProcInfo ()
    UsableGraph     :: Graph -> Set Vertex -> ProcInfo ()
    SCCGraph        :: Graph -> [Set Vertex] -> ProcInfo ()
    Polynomial      :: ProcInfo ()
    External        :: ExternalProc -> ProcInfo ()
    NarrowingP      :: (TRSC f, Ord id, Show id, T id :<: f) => NarradarTRS id f -> NarradarTRS id f -> ProcInfo id
    InstantiationP  :: (TRSC f, Ord id, Show id, T id :<: f) => NarradarTRS id f -> NarradarTRS id f -> ProcInfo id
    FInstantiationP :: (TRSC f, Ord id, Show id, T id :<: f) => NarradarTRS id f -> NarradarTRS id f -> ProcInfo id
    PrologP         :: ProcInfo ()
    PrologSKP       :: ProcInfo ()
    LabellingSKP    :: [Labelled String] -> ProcInfo ()
    PrologSKP_rhs   :: ProcInfo ()
    LabellingSKP_rhs:: ProcInfo ()
    UsableRulesNaiveP :: ProcInfo ()
    UsableRulesP    :: ProcInfo ()
    ReductionPair   :: Show id => Maybe (AF_ id) -> ProcInfo id
    Trivial         :: ProcInfo ()
    NoPairs         :: ProcInfo ()

isAFProc GroundOne{} = True
isAFProc GroundAll{} = True
isAFProc EVProc{}    = True
isAFProc GroundOne{} = True
isAFProc _           = False

instance Show id => Ppr (ProcInfo id) where
    ppr (DependencyGraph _) = text "Dependency Graph Processor (cycles)"
    ppr (UsableGraph _ _)   = text "Usable Graph Processor"
    ppr (SCCGraph    _ _)   = text "Dependency Graph Processor (SCCs)"
    ppr (External proc)     = text "External: " <> text (show proc)
    ppr (NarrowingP dp dps')= text "Narrowing Processor." $$
                                   text "Pair" <+> parens(ppr dp) <+> text "is replaced by:" $$
                                   ppr dps'
    ppr (InstantiationP dp dps')= text "Instantiation Processor." $$
                                   text "Pair" <+> parens(ppr dp) <+> text "is replaced by:" $$
                                   ppr dps'
    ppr (FInstantiationP dp dps')= text "Forward Instantiation Processor." $$
                                   text "Pair" <+> parens(ppr dp) <+> text "is replaced by:" $$
                                   ppr dps'
    ppr (GroundOne (Just pi)) = text "ICLP08 AF Processor" $$ ppr pi
    ppr (GroundAll (Just pi)) = text "All Rhs's Ground AF Processor" $$ ppr pi
    ppr (ReductionPair (Just pi)) = text "ICLP08 Reduction Pair Processor + Usable Rules" $$ ppr pi
    ppr (SafeAFP   (Just pi)) =  text "Safe AF Processor (infinitary constructor rewriting)" $$ ppr pi
    ppr (EVProc pi)      = text "Eliminate Extra Vars \n" $$ ppr pi
    ppr (isAFProc -> True) = text "Argument Filtering"
    ppr (Polynomial)     = text "Polynomial ordering"
    ppr PrologP          = text "Termination of LP as termination of Narrowing"
    ppr PrologSKP        = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation)"
    ppr (LabellingSKP mm)= text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + Labelling)" $$
                           text "Modes used " <> ppr (length mm) <> colon <+> (vcat $ map (hsep . map (text.show)) $ groupBy ((==) `on` unlabel) $ sort mm)
    ppr PrologSKP_rhs    = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + rhs bottoms trick)"
    ppr UsableRulesP     = text "Usable Rules for Basic Narrowing or Full Narrowing with constructor substitutions"
    ppr Trivial          = text "Trivially non terminating"
    ppr NoPairs          = text "Trivially terminating"

--pprLabellingAsMode (Labelled f mm) = text f <> parens (hsep $ punctuate comma [ if | m <- mm])

data ExternalProc = MuTerm | Aprove String | Other String   deriving Eq
instance Show ExternalProc where
    show (Aprove msg) = "Aprove " ++ msg
    show (Other  msg) = msg

-- ------
-- Modes
-- ------
type Goal = AF_ String
data Mode = G | V deriving (Eq, Bounded)
instance Show Mode where show G = "b"; show V = "f"

goalP =do
      spaces
      id <- Prolog.ident
      modes <- modesP
      return (AF.singleton id [i | (i,G) <- zip [1..] modes])

modesP = parens (modeP `sepBy` char ',') where parens= between (char '(') (char ')')
modeP = (oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V)

parseGoal :: String -> Either ParseError Goal
parseGoal = parse goalP ""

pprGoalAF :: (String ~ id, Ord id, Show id) => Signature id -> AF_ id -> Doc
pprGoalAF sig pi = vcat [ pprGoal (T f mm) | (f,pp) <- AF.toList pi
                                           , f `Set.member` allSymbols sig
                                           , let mm = [if i `elem` pp then G else V | i <- [1..getArity sig f] ]]

--type Goal id = T id Mode
pprGoal :: T String Mode -> Doc
pprGoal (T id modes) = text id <> parens(sep$ punctuate comma $ map (text.show) modes)



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
