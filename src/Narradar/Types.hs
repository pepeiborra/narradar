{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs, TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Narradar.Types ( module Narradar.Framework
                      , module Narradar.Constraints.Unify
                      , module Narradar.Types
                      , module Narradar.Types.TRS
                      , module Narradar.Types.Problem
                      , module Narradar.Types.Problem.Rewriting
                      , module Narradar.Types.Problem.Narrowing
                      , module Narradar.Types.Problem.NarrowingGen
                      , module Narradar.Types.Problem.Prolog
                      , module Narradar.Types.Problem.Relative
                      , module Narradar.Types.Problem.InitialGoal
                      , module Narradar.Types.Problem.NarrowingGoal
--                      , module Narradar.Types.Problem.NarrowingGen
                      , module Narradar.Types.Problem.Infinitary
                      , module Narradar.Types.DPIdentifiers
                      , module Narradar.Types.PrologIdentifiers
                      , module Narradar.Types.Labellings
                      , module Narradar.Types.Goal
                      , module Narradar.Types.Term
                      , module Narradar.Types.Var
                      , module Ppr
                      , HasTrie, Lattice
                      , AF_, simpleHeu, bestHeu, innermost
                      ) where

import Control.Applicative hiding (Alternative(..), many, optional)
import Control.Monad.Error (Error(..))
import Control.Monad (liftM, MonadPlus(..), (>=>))
import Data.Bifunctor
import Data.ByteString.Char8 (ByteString, unpack)
import Data.Graph (Graph, Vertex)
import Data.List (find, groupBy, maximumBy, sort, partition)
import Data.Foldable (Foldable(..))
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable as T
import Data.NarradarTrie (HasTrie)
import Lattice (Lattice)
import Text.ParserCombinators.Parsec
import qualified TRSParser as TRS
import qualified TRSTypes  as TRS
import TRSTypes hiding (Id, Rule, Term, TermF, Narrowing, Other, SimpleRuleF(..))
import Prelude as P hiding (mapM, pi, sum)


import MuTerm.Framework.DotRep
import MuTerm.Framework.Strategy
import MuTerm.Framework.Output

import Narradar.Constraints.Unify
import Narradar.Types.ArgumentFiltering (AF_, simpleHeu, bestHeu, innermost)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers         hiding (ArityId(..), StringId)
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Labellings
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing
import Narradar.Types.Problem.NarrowingGen  hiding (baseProblem)
import Narradar.Types.Problem.NarrowingGoal hiding (baseProblem, goal)
import Narradar.Types.Problem.Prolog        hiding (goals)
import Narradar.Types.Problem.Relative      hiding (baseProblem, baseProblemType)
import Narradar.Types.Problem.InitialGoal   hiding (baseProblem, baseProblemType, goals)
import Narradar.Types.Problem.Infinitary    hiding (pi, baseProblem, baseProblemType, pi_PType)
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr

import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.Parser as Prolog hiding (term)

#ifdef HOOD
import Debug.Observe
#endif

import Prelude as P hiding (sum, pi, mapM)

data Output = OutputXml ByteString | OutputHtml ByteString | OutputTxt ByteString deriving Show

isOutputTxt OutputTxt{} = True; isOutputTxt _ = False
isOutputXml OutputXml{} = True; isOutputXml _ = False
isOutputHtml OutputHtml{} = True; isOutputHtml _ = False
{-
instance Pretty [Output] where
    pPrint outputs
        | Just (OutputTxt txt) <- find isOutputTxt outputs = text (unpack txt)
        | otherwise = Ppr.empty
-}
-- --------------------
-- The Narradar Parser
-- --------------------

narradarParse name input = let
    results = map (\p -> runParser p mempty name input) [trsParser, APrologProblem <$> prologParser]
    in case results of
         [Right x, _] -> Right x
         [_, Right x] -> Right x
         [Left e1 , Left e2] -> Left $ bestError [e1,e2]

bestError :: [ParseError] -> ParseError
bestError = maximumBy (compare `on` errorPos)
 where on cmp f x y = f x `cmp` f y

-- ---------------------------------
-- Parsing and dispatching TPDB TRSs
-- ---------------------------------

class Dispatch thing where
    dispatch :: (Traversable m, MonadPlus m) => thing -> Proof (PrettyInfo, DotInfo) m FinalProcessor

mkDispatcher :: Monad m => (a -> Proof info m b) ->  a -> Proof info m FinalProcessor
mkDispatcher f =  f >=> final

data AProblem t trs where
    ARewritingProblem         :: Problem Rewriting trs  -> AProblem t trs
    AIRewritingProblem        :: Problem IRewriting trs -> AProblem t trs
    ANarrowingProblem         :: Problem Narrowing trs  -> AProblem t trs
    ACNarrowingProblem        :: Problem CNarrowing trs -> AProblem t trs
    ARelativeRewritingProblem :: Problem (Relative trs Rewriting) trs -> AProblem t trs
    ARelativeIRewritingProblem     :: Problem (Relative trs IRewriting) trs -> AProblem t trs
    AGoalRelativeRewritingProblem  :: Problem (Relative trs (InitialGoal t Rewriting)) trs  -> AProblem t trs
    AGoalRelativeIRewritingProblem :: Problem (Relative trs (InitialGoal t IRewriting)) trs -> AProblem t trs
    AGoalRewritingProblem     :: Problem (InitialGoal t Rewriting) trs  -> AProblem t trs
    AGoalIRewritingProblem    :: Problem (InitialGoal t IRewriting) trs -> AProblem t trs
    AGoalNarrowingProblem     :: Problem (NarrowingGoal (TermId t)) trs -> AProblem t trs
    AGoalCNarrowingProblem    :: Problem (CNarrowingGoal (TermId t)) trs -> AProblem t trs
    APrologProblem            :: PrologProblem -> AProblem t trs
--    AGoalNarrowingRelativeRewritingProblem :: Problem (Relative trs NarrowingGoal (TermId t)) trs -> AProblem t trs


dispatchAProblem :: (Traversable m, MonadPlus m
                    ,Dispatch (Problem Rewriting  trs)
                    ,Dispatch (Problem IRewriting trs)
                    ,Dispatch (Problem (InitialGoal t Rewriting) trs)
                    ,Dispatch (Problem (InitialGoal t IRewriting) trs)
                    ,Dispatch (Problem (Relative  trs (InitialGoal t Rewriting))  trs)
                    ,Dispatch (Problem (Relative  trs (InitialGoal t IRewriting))  trs)
                    ,Dispatch (Problem (Relative  trs Rewriting)  trs)
                    ,Dispatch (Problem (Relative  trs IRewriting)  trs)
                    ,Dispatch (Problem Narrowing  trs)
                    ,Dispatch (Problem CNarrowing trs)
                    ,Dispatch (Problem (NarrowingGoal (TermId t)) trs)
                    ,Dispatch (Problem (CNarrowingGoal (TermId t)) trs)
                    ,Dispatch PrologProblem
                    ) => AProblem t trs -> Proof  (PrettyInfo, DotInfo) m FinalProcessor

dispatchAProblem (ARewritingProblem p)         = dispatch p
dispatchAProblem (AIRewritingProblem p)        = dispatch p
dispatchAProblem (ANarrowingProblem p)         = dispatch p
dispatchAProblem (ACNarrowingProblem p)        = dispatch p
dispatchAProblem (ARelativeRewritingProblem p) = dispatch p
dispatchAProblem (ARelativeIRewritingProblem p)= dispatch p
dispatchAProblem (AGoalRewritingProblem p)     = dispatch p
dispatchAProblem (AGoalIRewritingProblem p)    = dispatch p
dispatchAProblem (AGoalNarrowingProblem p)     = dispatch p
dispatchAProblem (AGoalCNarrowingProblem p)    = dispatch p
dispatchAProblem (APrologProblem p)            = dispatch p
dispatchAProblem (AGoalRelativeRewritingProblem p) = dispatch p
dispatchAProblem (AGoalRelativeIRewritingProblem p)= dispatch p



parseTRS :: (trs ~ NTRS Id, Monad m) =>
             String -> m (AProblem (TermF Id) trs)
parseTRS s = eitherM (runParser trsParser mempty "<input>" s)

trsParser :: TRS.TRSParser (AProblem (TermF Id) (NTRS Id))
trsParser = do
  Spec spec <- TRS.trsParser

  let allvars = Map.fromList (Set.toList(getVars spec) `zip` [0..])
      toTerm  = foldTerm toVar (Impure . fromSimple)
      toVar v = var' (Just v) (fromJust $ Map.lookup v allvars)

      spec'   = toTerm <$$> spec

      strategies = sort [s | Strategy s <- spec']
      minimality = if TRSTypes.Any (Just "MINIMALITY") [] `elem` spec
                    then M
                    else A

  let r   = [ l :-> r  | Rules rr <- spec', TRS.Rule (l TRS.:->  r) _ <- rr]
      r0  = [ mapTermSymbols IdFunction l :-> mapTermSymbols IdFunction r
                  | Rules rr <- spec', TRS.Rule (l TRS.:->= r) _ <- rr]
      dps = [markDPRule (mapTermSymbols IdFunction l :-> mapTermSymbols IdFunction r)
                  | Pairs rr <- spec', TRS.Rule (l TRS.:-> r) _ <- rr]
      r' = mkTRS (mapTermSymbols IdFunction <$$> r)

      mkGoal = markDP . mapTermSymbols IdFunction

--      mkAbstractGoal :: Monad m => Term String -> m (Goal Id)
      mkAbstractGoal (Impure (Term id tt)) = do {tt' <- mapM mkMode tt; return (Goal (IdDP id) tt')}
      mkMode (Impure (Term (the_id -> "i") [])) = return G
      mkMode (Impure (Term (the_id -> "b") [])) = return G
      mkMode (Impure (Term (the_id -> "c") [])) = return G
      mkMode (Impure (Term (the_id -> "g") [])) = return G
      mkMode (Impure (Term (the_id -> "o") [])) = return V
      mkMode (Impure (Term (the_id -> "v") [])) = return V
      mkMode (Impure (Term (the_id -> "f") [])) = return V
      mkMode _                      = fail "parsing the abstract goal"

  case (r0, dps, strategies) of
    ([], [], [])
        -> return $ ARewritingProblem (mkNewProblem rewriting r)
    ([], [], TRS.Narrowing:_)        -> return $ ANarrowingProblem (mkNewProblem narrowing r)
    ([], [], ConstructorNarrowing:_) -> return $ ACNarrowingProblem (mkNewProblem cnarrowing r)
    ([], [], InnerMost:TRS.Narrowing:_)  -> return $ ACNarrowingProblem (mkNewProblem cnarrowing r)

    ([], [], [GoalStrategy g])
        -> return $ AGoalRewritingProblem (mkNewProblem (initialGoal [mkGoal g] rewriting) r)

    ([], [], InnerMost:_)
        -> return $ AIRewritingProblem (mkNewProblem irewriting r)


    ([], [], GoalStrategy g:TRS.Narrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalNarrowingProblem (mkNewProblem (narrowingGoal g') r)}
--    (r0, [], GoalStrategy g:TRS.Narrowing:_)
--        -> do {g' <- mkAbstractGoal g; return $ AGoalNarrowingRelativeRewritingProblem
--                                                (mkNewProblem (relative (tRS r0) (narrowingGoal g')) r)}
    ([], [], GoalStrategy g:ConstructorNarrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalCNarrowingProblem (mkNewProblem (cnarrowingGoal g') r)}
    ([], [], GoalStrategy g:InnerMost:TRS.Narrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalCNarrowingProblem (mkNewProblem (cnarrowingGoal g') r)}
    ([], [], (GoalStrategy g : InnerMost : _))
        -> return $ AGoalIRewritingProblem (mkNewProblem (initialGoal [mkGoal g] irewriting) r)
    ([], dps, [])
        -> return $ ARewritingProblem (setMinimality minimality $ mkDPProblem rewriting r' (mkTRS dps))

    ([], dps, [GoalStrategy g])
        -> return $ AGoalRewritingProblem (setMinimality minimality $ mkDPProblem (initialGoal [mkGoal g] rewriting) r' (tRS dps))

    ([], dps, InnerMost:_)
        -> return $ AIRewritingProblem (setMinimality minimality $ mkDPProblem irewriting r' (tRS dps))
    ([], dps, GoalStrategy g:InnerMost:_)
        -> return $ AGoalIRewritingProblem (setMinimality minimality $ mkDPProblem (initialGoal [mkGoal g] irewriting) r' (tRS dps))

    (r0, [], [])
        -> return $ ARelativeRewritingProblem (mkNewProblem (relative (tRS r0) rewriting) r)
    (r0, [], InnerMost:_)
        -> return $ ARelativeIRewritingProblem (mkNewProblem (relative (tRS r0) irewriting) r)


    (r0, [], [GoalStrategy g])
        -> return $ AGoalRelativeRewritingProblem (mkNewProblem (relative (tRS r0) (initialGoal [mkGoal g] rewriting)) r)
    (r0, [], GoalStrategy g:InnerMost:_)
        -> return $ AGoalRelativeIRewritingProblem (mkNewProblem (relative (tRS r0) (initialGoal [mkGoal g] irewriting)) r)


    (r0, dps, [])
        -> return $ ARelativeRewritingProblem (setMinimality minimality $
                                               mkDPProblem (relative (tRS r0) rewriting) r' (tRS dps))

    (r0, dps, InnerMost:_)
        -> return $ ARelativeIRewritingProblem (setMinimality minimality $
                                                mkDPProblem (relative (tRS r0) irewriting) r' (tRS dps))
    (r0, dps, [GoalStrategy g])
        -> return $ AGoalRelativeRewritingProblem
                  $ setMinimality A
                  $ mkDPProblem (relative (tRS r0) (initialGoal [mkGoal g] rewriting)) r' (mkTRS dps)

    (r0, dps, GoalStrategy g:InnerMost:_)
        -> return $ AGoalRelativeIRewritingProblem
                  $ mkDPProblem (relative (tRS r0) (initialGoal [mkGoal g] irewriting)) r' (mkTRS dps)

    _   -> fail "Invalid combination of rules, pairs and/or goals"
-- ------------
-- Debug stuff
-- ------------
#ifdef HOOD
instance Observable Mode where observer = observeBase
#endif
