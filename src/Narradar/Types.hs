{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs, TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types ( module Narradar.Constraints.Unify
                      , module Narradar.Types
                      , module Narradar.Types.DPairs
                      , module Narradar.Types.TRS
                      , module Narradar.Types.Problem
                      , module Narradar.Types.ProblemType
                      , module Narradar.Types.DPIdentifiers
                      , module Narradar.Types.PrologIdentifiers
                      , module Narradar.Types.Labellings
                      , module Narradar.Types.Goal
                      , module Narradar.Types.Term
                      , module Narradar.Types.Var
                      , module Narradar.Utils.Convert
                      , module Narradar.Utils.Ppr
                      ) where
import Data.DeriveTH
import Data.Derive.Is

import Control.Applicative hiding (Alternative(..), many, optional)
import Control.Monad.Error (Error(..))
import Control.Monad (MonadPlus(..))
import Data.ByteString.Char8 (ByteString)
import Data.Graph (Graph, Vertex)
import Data.List (groupBy, sort, partition)
import Data.Foldable (Foldable(..))
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable as T
import Text.ParserCombinators.Parsec
import Text.PrettyPrint hiding (char, Mode)
import qualified Text.PrettyPrint as Ppr
import qualified TRSParser
import TRSTypes (Mode(..))
import Prelude as P hiding (mapM, pi, sum)

import Narradar.Constraints.Unify
import Narradar.Types.ArgumentFiltering (AF_)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPairs
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Labellings
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.ProblemType
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils.Convert
import Narradar.Utils
import Narradar.Utils.Ppr

import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.Parser as Prolog

#ifdef DEBUG
import Debug.Observe
#endif

import Prelude as P hiding (sum, pi, mapM)

isGround :: (Functor t, Foldable t) => Term t v -> Bool
isGround = null . vars

-- ------------
-- Processors
-- ------------
data ProcInfo id where                    -- vv ignored vv
    GroundOne       :: Ppr id => Maybe (AF_ id) -> ProcInfo id
    GroundAll       :: Ppr id => Maybe (AF_ id) -> ProcInfo id
    SafeAFP         :: Ppr id => Maybe (AF_ id) -> ProcInfo id
    EVProc          :: Ppr id => AF_ id -> ProcInfo id
    EVProcFail      :: ProcInfo ()
    DependencyGraph :: Graph -> ProcInfo ()
    UsableGraph     :: Graph -> Set Vertex -> ProcInfo ()
    SCCGraph        :: Graph -> [Set Vertex] -> ProcInfo ()
    NoCycles        :: ProcInfo ()
    NarrowingP      :: (Ord id, Ord v, Ppr v, Ppr id) => NarradarTRS id v -> NarradarTRS id v -> ProcInfo id
    InstantiationP  :: (Ord id, Ord v, Ppr v, Ppr id) => NarradarTRS id v -> NarradarTRS id v -> ProcInfo id
    FInstantiationP :: (Ord id, Ord v, Ppr v, Ppr id) => NarradarTRS id v -> NarradarTRS id v -> ProcInfo id
    PrologP         :: ProcInfo ()
    PrologSKP       :: ProcInfo ()
    LabellingSKP    :: (Ppr id, Ord id) => [Labelled id] -> ProcInfo id
    LabellingCP     :: (Ppr id, Ord id) => [Labelled id] -> ProcInfo id
    PrologSKP_rhs   :: ProcInfo ()
    LabellingSKP_rhs:: ProcInfo ()
    UsableRulesNaiveP :: ProcInfo ()
    UsableRulesP    :: ProcInfo ()
    ReductionPair   :: Ppr id => Maybe (AF_ id) -> ByteString ->ProcInfo id
    NonTerminationLooping :: ProcInfo ()
    GenTransformation :: [RuleN id v] -> ProcInfo ()
    NoPairs         :: ProcInfo ()
    External        :: ExternalProc -> [Output] -> ProcInfo ()

isAFProc GroundOne{} = True
isAFProc GroundAll{} = True
isAFProc EVProc{}    = True
isAFProc GroundOne{} = True
isAFProc _           = False

instance Ppr id => Ppr (ProcInfo id) where
    ppr (DependencyGraph _) = text "Dependency Graph Processor (cycles)"
    ppr (UsableGraph _ _)   = text "Usable Graph Processor"
    ppr (SCCGraph    _ _)   = text "Dependency Graph Processor (SCCs)"
    ppr NoCycles            = text "We need to prove termination for all the cycles. There are no cycles, so the system is terminating"
    ppr (External proc _)   = text "External: " <> text (show proc)
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
    ppr (ReductionPair (Just pi) _) = text "ICLP08 Reduction Pair Processor + Usable Rules" $$ ppr pi
    ppr (SafeAFP   (Just pi)) =  text "Safe AF Processor (infinitary constructor rewriting) + Usable Rules" $$ ppr pi
    ppr (EVProc pi)           = text "Eliminate Extra Vars \n" $$ ppr pi
    ppr  EVProcFail           = text "There is no argument filtering which enforces the variable condition" -- impossible?
    ppr (isAFProc -> True)    = text "Argument Filtering"
    ppr PrologP          = text "Termination of LP as termination of Narrowing"
    ppr PrologSKP        = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation)"
    ppr (LabellingSKP mm)= text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + Predicate Labelling)" $$
                           text "Modes used " <> ppr (length mm) <> colon <+> (fsep $ map ppr $ sort mm)
    ppr (LabellingCP mm) = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + Constructor Labelling)" $$
                           text "Modes used " <> ppr (length mm) <> colon <+> (fsep $ map ppr $ sort mm)
    ppr PrologSKP_rhs    = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + rhs bottoms trick)"
    ppr UsableRulesP     = text "Usable Rules for Basic Narrowing or Full Narrowing with constructor substitutions"
    ppr NonTerminationLooping = text "Trivially non terminating"
    ppr GenTransformation{} = text "Transformation of extra variables to generators"
    ppr NoPairs          = text "Trivially terminating"

--pprLabellingAsMode (Labelled f mm) = text f <> parens (hsep $ punctuate comma [ if | m <- mm])

data ExternalProc = MuTerm | Aprove String | Other String deriving Eq
instance Show ExternalProc where
    show (Aprove msg) = "Aprove " ++ msg
    show (Other  msg) = msg

data Output = OutputXml ByteString | OutputHtml ByteString | OutputTxt ByteString deriving Show
--instance Monoid Output where

$(derive makeIs ''Output)

-- ---------------------
-- Specific to narrowing
-- ---------------------
-- TODO move to a more appropriate place

correspondingRewritingStrategy Narrowing = Rewriting
correspondingRewritingStrategy GNarrowing = InnermostRewriting
correspondingRewritingStrategy BNarrowing = Rewriting
correspondingRewritingStrategy NarrowingModes{} = Rewriting
correspondingRewritingStrategy GNarrowingModes{} = InnermostRewriting
correspondingRewritingStrategy BNarrowingModes{} = Rewriting


-- --------------------------
-- Parsing Prolog problems
-- --------------------------
data PrologSection = Query [Prolog.Goal String] | Clause (Prolog.Clause String) | QueryString String

problemParser = do
  txt <- getInput
  let !queryComments = map QueryString $ catMaybes $ map f (lines txt)
  res <- Prolog.whiteSpace >> concat <$> many (Clause <$$> Prolog.clause <|> Query <$$> Prolog.query)
  return (res ++ queryComments)
  where f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
        f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
        f _ = Nothing

data ErrorM e a = L e | R a

instance Monad (ErrorM e) where
  return = R
  L e >>= _ = L e
  R a >>= f = f a

instance Error e => MonadPlus (ErrorM e) where
  mzero = L noMsg
  mplus (R x) _ = R x
  mplus _     r = r

instance Error ParseError

instance Functor (ErrorM e) where fmap _ (L e) = L e; fmap f (R x) = R (f x)

-- Workaround an inability of GHC to hide instances
-- MonadError Instances for Either from mtl and monads-fd clash
fromEither = either L R
toEither (L l) = Left l; toEither (R r) = Right r


parsePrologProblem :: (Ord v) => String -> ErrorM ParseError (Problem String v)
parsePrologProblem pgm = do
     things <- fromEither $ parse problemParser "input" pgm
     let cc      = [c | Clause      c <- things]
         gg1     = [q | Query       q <- things]
         gg_txt  = [q | QueryString q <- things]
     gg2    <- concat <$> mapM (fromEither.parseGoal) gg_txt
     gg1'   <- mapM atomToGoal (concat gg1)
     let sig   = getSignature cc
         (constructor_goals, defined_goals) = partition ((`Set.member` getConstructorSymbols sig) . fst) (gg1' ++ gg2)
         constructor_af = AF.fromList [(f, ii) | (f, mm) <- constructor_goals, let ii = [ i | (i,G) <- zip [1..] mm]]
         goals = [constructor_af `mappend`
                  AF.singleton f ii | (f, mm) <- defined_goals, let ii = [ i | (i,G) <- zip [1..] mm]]
     return (mkPrologProblem goals cc)
 where
     atomToGoal (Prolog.Pred f tt) = do
       mm <- fromEither $ parse TRSParser.modes "" $ unwords $ map (show . Prolog.ppr) $ tt
       return (f,mm)

#ifdef DEBUG
instance Observable Mode where observer = observeBase
#endif
