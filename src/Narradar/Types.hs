{-# LANGUAGE GADTs, TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PackageImports #-}

module Narradar.Types ( module TRS
                      , module Narradar.Types
                      , module Narradar.TRS
                      , module Narradar.Problem
                      , module Narradar.ProblemType
                      , module Narradar.DPIdentifiers
                      , module Narradar.PrologIdentifiers
                      , module Narradar.Labellings
                      , module Narradar.Convert
                      , module Narradar.Unify
                      ) where
import Data.DeriveTH
import Data.Derive.Is

import Control.Applicative hiding (Alternative(..), many, optional)
import Control.Monad.Error (Error(..), noMsg)
import Control.Monad (MonadPlus(..))
import Data.Graph (Graph, Vertex)
import Data.List ((\\), groupBy, sort, partition)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable as T
import Text.ParserCombinators.Parsec
import Text.PrettyPrint hiding (char, Mode)
import qualified Text.PrettyPrint as Ppr
import Text.XHtml (Html)
import Prelude as P hiding (mapM, pi, sum)

import Narradar.ArgumentFiltering (AF, AF_, ApplyAF(..), init)
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.Problem
import Narradar.ProblemType
import Narradar.TRS
import Narradar.Convert
import Narradar.Utils
import Narradar.Unify

import TRS hiding (ppr, Ppr, unify, unifies)
import TRS.FetchRules ()
import qualified TRS
import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.Parser as Prolog
import Prelude as P hiding (sum, pi, mapM)

isGround :: TRSC f => Term f -> Bool
isGround = null . vars

-- ------------
-- Processors
-- ------------
data ProcInfo id where                    -- vv ignored vv
    GroundOne       :: Show id => Maybe (AF_ id) -> ProcInfo id
    GroundAll       :: Show id => Maybe (AF_ id) -> ProcInfo id
    SafeAFP         :: Show id => Maybe (AF_ id) -> ProcInfo id
    EVProc          :: Show id => AF_ id -> ProcInfo id
    EVProcFail      :: ProcInfo ()
    DependencyGraph :: Graph -> ProcInfo ()
    UsableGraph     :: Graph -> Set Vertex -> ProcInfo ()
    SCCGraph        :: Graph -> [Set Vertex] -> ProcInfo ()
    NoCycles        :: ProcInfo ()
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
    NonTerminationLooping :: ProcInfo ()
    NoPairs         :: ProcInfo ()
    External        :: ExternalProc -> [Output] -> ProcInfo ()

isAFProc GroundOne{} = True
isAFProc GroundAll{} = True
isAFProc EVProc{}    = True
isAFProc GroundOne{} = True
isAFProc _           = False

instance Show id => Ppr (ProcInfo id) where
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
    ppr (ReductionPair (Just pi)) = text "ICLP08 Reduction Pair Processor + Usable Rules" $$ ppr pi
    ppr (SafeAFP   (Just pi)) =  text "Safe AF Processor (infinitary constructor rewriting)" $$ ppr pi
    ppr (EVProc pi)           = text "Eliminate Extra Vars \n" $$ ppr pi
    ppr  EVProcFail           = text "There is no argument filtering which enforces the variable condition" -- impossible?
    ppr (isAFProc -> True)    = text "Argument Filtering"
    ppr PrologP          = text "Termination of LP as termination of Narrowing"
    ppr PrologSKP        = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation)"
    ppr (LabellingSKP mm)= text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + Labelling)" $$
                           text "Modes used " <> ppr (length mm) <> colon <+> (vcat $ map (hsep . map (text.show)) $ groupBy ((==) `on` unlabel) $ sort mm)
    ppr PrologSKP_rhs    = text "Termination of LP as termination of Narrowing" $$
                           text "(Schneider-Kamp transformation + rhs bottoms trick)"
    ppr UsableRulesP     = text "Usable Rules for Basic Narrowing or Full Narrowing with constructor substitutions"
    ppr NonTerminationLooping = text "Trivially non terminating"
    ppr NoPairs          = text "Trivially terminating"

--pprLabellingAsMode (Labelled f mm) = text f <> parens (hsep $ punctuate comma [ if | m <- mm])

data ExternalProc = MuTerm | Aprove String | Other String   deriving Eq
instance Show ExternalProc where
    show (Aprove msg) = "Aprove " ++ msg
    show (Other  msg) = msg

data Output = OutputXml String | OutputHtml Html | OutputTxt String deriving Show
--instance Monoid Output where

$(derive makeIs ''Output)
-- ------
-- Modes
-- ------
type Goal = (String, [Mode])
data Mode = G | V deriving (Eq, Bounded)
instance Show Mode where show G = "b"; show V = "f"

goalP =do
      id <- Prolog.ident
      modes <- modesP
      optional (char '.')
      return (id, modes)

modesP = parens (modeP `sepBy` char ',') where parens= between (char '(') (char ')')
modeP = (oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V)

parseGoal :: String -> Either ParseError [Goal]
parseGoal = parse (Prolog.whiteSpace >> many (goalP <* Prolog.whiteSpace)) ""

mkGoalAF (f, tt) = AF.singleton f [ i | (i,G) <- zip [1..] tt]

pprGoalAF :: (String ~ id, Ord id, Show id) => Signature id -> AF_ id -> Doc
pprGoalAF sig pi = vcat [ pprGoal (f, mm) | (f,pp) <- AF.toList pi
                                           , f `Set.member` allSymbols sig
                                           , let mm = [if i `elem` pp then G else V | i <- [1..getArity sig f] ]]

--type Goal id = T id Mode
pprGoal :: Goal -> Doc
pprGoal (id, modes) = text id <> parens(sep$ punctuate comma $ map (text.show) modes)


-- --------------------------
-- Parsing Prolog problems
-- --------------------------
data PrologSection = Query [Prolog.Goal String] | Clause (Prolog.Clause String) | QueryString String

problemParser = do
  txt <- getInput
  let !queryComments = map QueryString $ catMaybes $ map f (lines txt)
  res <- Prolog.whiteSpace >> many (Clause <$> Prolog.clause <|> Query <$> Prolog.query)
  return (res ++ queryComments)
  where f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
        f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
        f _ = Nothing

data ErrorM e a = L e | R a

instance Monad (ErrorM e) where
  return = R
  L e >>= f = L e
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

--mkPrologProblem = (return.) . mkPrologProblem
parsePrologProblem pgm = do
     things <- fromEither $ parse problemParser "input" pgm
     let cc      = [c | Clause      c <- things]
         gg1     = [q | Query       q <- things]
         gg_txt  = [q | QueryString q <- things]
     gg2    <- concat <$> mapM (fromEither.parseGoal) gg_txt
     gg1'   <- mapM atomToGoal (concat gg1)
     let sig   = getSignature cc
         (constructor_goals, defined_goals) = partition ((`Set.member` constructorSymbols sig) . fst) (gg1' ++ gg2)
         constructor_af = AF.fromList [(f, ii) | (f, mm) <- constructor_goals, let ii = [ i | (i,G) <- zip [1..] mm]]
         goals = [constructor_af `mappend`
                  AF.singleton f ii | (f, mm) <- defined_goals, let ii = [ i | (i,G) <- zip [1..] mm]]
     return (mkPrologProblem goals cc)
 where
     atomToGoal (Prolog.Pred f tt) = do
       mm <- fromEither $ parse modesP "" $ unwords $ map (show . Prolog.ppr) $ tt
       return (f,mm)