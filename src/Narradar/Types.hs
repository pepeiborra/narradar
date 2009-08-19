{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs, TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances,UndecidableInstances #-}
{-# LANGUAGE ImpredicativeTypes, RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.Types ( module MuTerm.Framework.Problem
                      , module Narradar.Constraints.Unify
                      , module Narradar.Types
                      , module Narradar.Types.TRS
                      , module Narradar.Types.Problem
                      , module Narradar.Types.Problem.Rewriting
                      , module Narradar.Types.Problem.Narrowing
                      , module Narradar.Types.Problem.Prolog
                      , module Narradar.Types.Problem.Prolog
                      , module Narradar.Types.Problem.Relative
                      , module Narradar.Types.Problem.InitialGoal
                      , module Narradar.Types.Problem.NarrowingGoal
                      , module Narradar.Types.Problem.Infinitary
                      , module Narradar.Types.DPIdentifiers
                      , module Narradar.Types.PrologIdentifiers
                      , module Narradar.Types.Labellings
                      , module Narradar.Types.Goal
                      , module Narradar.Types.Term
                      , module Narradar.Types.Var
                      , module Narradar.Framework.Ppr
                      ) where
import Data.DeriveTH
import Data.Derive.Is

import Control.Applicative hiding (Alternative(..), many, optional)
import Control.Monad.Error (Error(..))
import Control.Monad (MonadPlus(..))
import Data.ByteString.Char8 (ByteString, unpack)
import Data.Graph (Graph, Vertex)
import Data.List (find, groupBy, sort, partition)
import Data.Foldable (Foldable(..))
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable as T
import Text.ParserCombinators.Parsec
import Text.PrettyPrint as Doc hiding (char, Mode)
import qualified Text.PrettyPrint as Ppr
import qualified TRSParser as TRS
import qualified TRSTypes  as TRS
import TRSTypes hiding (Goal, Id, Rule, Term, TermF, Narrowing, Other, SimpleRuleF(..))
import Prelude as P hiding (mapM, pi, sum)

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Constraints.Unify
import Narradar.Types.ArgumentFiltering (AF_)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Labellings
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Problem.NarrowingGoal hiding (pi, baseProblem, baseProblemType, pi_PType)
import Narradar.Types.Problem.Prolog        hiding (goals)
import Narradar.Types.Problem.Relative      hiding (baseProblem, baseProblemType)
import Narradar.Types.Problem.InitialGoal   hiding (baseProblem, baseProblemType, goals)
import Narradar.Types.Problem.Infinitary    hiding (pi, baseProblem, baseProblemType, pi_PType)
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr

import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.Parser as Prolog

#ifdef DEBUG
import Debug.Observe
#endif

import Prelude as P hiding (sum, pi, mapM)

isGround :: (Functor t, Foldable t) => Term t v -> Bool
isGround = null . vars

collapsing trs = any (isVar.rhs) (rules trs)

data Output = OutputXml ByteString | OutputHtml ByteString | OutputTxt ByteString deriving Show

$(derive makeIs ''Output)

instance Ppr [Output] where
    ppr outputs
        | Just (OutputTxt txt) <- find isOutputTxt outputs = text (unpack txt)
        | otherwise = Doc.empty

-- -----------------
-- Parsing TPDB TRSs
-- -----------------

data AProblem id trs where
    ARewritingProblem   :: DPProblem Rewriting trs  -> AProblem id trs
    AIRewritingProblem  :: DPProblem IRewriting trs -> AProblem id trs
    ANarrowingProblem   :: DPProblem Narrowing trs  -> AProblem id trs
    ACNarrowingProblem  :: DPProblem CNarrowing trs -> AProblem id trs
    ARelativeRewritingProblem :: DPProblem (Relative trs Rewriting) trs -> AProblem id trs
    AGoalNarrowingProblem :: DPProblem (InitialGoal id Narrowing) trs -> AProblem id trs
    AGoalCNarrowingProblem :: DPProblem (InitialGoal id CNarrowing) trs -> AProblem id trs

dispatchAProblem (ARewritingProblem p)         = dispatch p
dispatchAProblem (AIRewritingProblem p)        = dispatch p
dispatchAProblem (ANarrowingProblem p)         = dispatch p
dispatchAProblem (ACNarrowingProblem p)        = dispatch p
dispatchAProblem (ARelativeRewritingProblem p) = dispatch p
dispatchAProblem (AGoalNarrowingProblem p)     = dispatch p
dispatchAProblem (AGoalCNarrowingProblem p)    = dispatch p


parseTRS :: (trs ~ NarradarTRS id Var, id ~ Identifier String, Monad m) =>
             String -> m (AProblem id trs)
parseTRS s = eitherM (runParser trsParser mempty "<input>" s)

trsParser :: ( v   ~ Var
             , id  ~ Identifier String
             , trs ~ NarradarTRS id v
             ) => TRS.TRSParser (AProblem id trs)

trsParser = do
  Spec spec <- TRS.trsParser

  let allvars = Map.fromList (Set.toList(getVars spec) `zip` [0..])
      toTerm  = foldTerm toVar (Impure . fromSimple)
      toVar v = var' (Just v) (fromJust $ Map.lookup v allvars)

      spec'   = toTerm <$$$> spec

      strategy = [s | Strategy s <- spec]

  let r   = [ l :-> r  | Rules rr <- spec', TRS.Rule (l TRS.:->  r) _ <- rr]
      r0  = [ l :-> r  | Rules rr <- spec', TRS.Rule (l TRS.:->= r) _ <- rr]
      dps = [markDPRule (mapTermSymbols IdFunction l :-> mapTermSymbols IdFunction r)
                            | Pairs rr <- spec', TRS.Rule (l TRS.:-> r) _ <- rr]
      r' = tRS$ mapTermSymbols IdFunction <$$> r

  case (r0, dps, strategy) of
    ([], [], [])
        -> return $ ARewritingProblem (mkNarradarProblem Rewriting r)

    ([], [], [InnerMost])
        -> return $ AIRewritingProblem (mkNarradarProblem IRewriting r)

    ([], dps, [])
        -> return $ ARewritingProblem (mkDPProblem Rewriting r' (tRS dps))

    ([], dps, [InnerMost])
        -> return $ AIRewritingProblem (mkDPProblem IRewriting r' (tRS dps))

    (r0, [], [])
        -> return $ ARelativeRewritingProblem (mkNarradarProblem (Relative r0 Rewriting) r)

    ([], [], [TRS.Narrowing])
        -> return $ ANarrowingProblem (mkNarradarProblem Narrowing r)

    ([], [], [ConstructorNarrowing])
        -> return $ ACNarrowingProblem (mkNarradarProblem CNarrowing r)

    ([], [], [NarrowingG (TRS.Term id tt)])
        -> return $ AGoalNarrowingProblem (mkNarradarProblem (initialGoal [Goal id tt] Narrowing) r)

    ([], [], [ConstructorNarrowingG (TRS.Term id tt)])
        -> return $ AGoalCNarrowingProblem (mkNarradarProblem (initialGoal [Goal id tt] CNarrowing) r)


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


parsePrologProblem :: String -> ErrorM ParseError PrologProblem
parsePrologProblem pgm = do
     things <- fromEither $ parse problemParser "input" pgm
     let cc      = [c | Clause      c <- things]
         gg1     = [q | Query       q <- things]
         gg_txt  = [q | QueryString q <- things]
     gg2    <- concat <$> mapM (fromEither.parseGoal) gg_txt
     gg1'   <- mapM atomToGoal (concat gg1)
     let sig   = getSignature cc
         (constructor_goals, defined_goals) = partition ((`Set.member` getConstructorSymbols sig) . goalId) (gg1' ++ gg2)
         constructor_af = AF.fromList [(f, ii) | (Goal f mm) <- constructor_goals, let ii = [ i | (i,G) <- zip [1..] mm]]
         goals = [constructor_af `mappend`
                  AF.singleton f ii | (Goal f mm) <- defined_goals, let ii = [ i | (i,G) <- zip [1..] mm]]
     return (prologProblem goals cc)
 where
     atomToGoal (Prolog.Pred f tt) = do
       mm <- fromEither $ parse TRS.modes "" $ unwords $ map (show . Prolog.ppr) $ tt
       return (Goal f mm)

#ifdef DEBUG
instance Observable Mode where observer = observeBase
#endif
