{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs, TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

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
                      ) where
import Data.DeriveTH
import Data.Derive.Is

import Control.Applicative hiding (Alternative(..), many, optional)
import Control.Monad.Error (Error(..))
import Control.Monad (liftM, MonadPlus(..))
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
import qualified TRSParser as TRS
import qualified TRSTypes  as TRS
import TRSTypes hiding (Id, Rule, Term, TermF, Narrowing, Other, SimpleRuleF(..))
import Prelude as P hiding (mapM, pi, sum)


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
import Narradar.Framework hiding (Label, Note)
import Narradar.Framework.Ppr as Ppr

import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import qualified Language.Prolog.Parser as Prolog

#ifdef HOOD
import Debug.Observe
#endif

import Prelude as P hiding (sum, pi, mapM)

data Output = OutputXml ByteString | OutputHtml ByteString | OutputTxt ByteString deriving Show

$(derive makeIs ''Output)

instance Pretty [Output] where
    pPrint outputs
        | Just (OutputTxt txt) <- find isOutputTxt outputs = text (unpack txt)
        | otherwise = Ppr.empty

-- --------------------
-- The Narradar Parser
-- --------------------

narradarParser = trsParser <|> prologParser' where
  prologParser' = do
    p <- prologParser
    return (APrologProblem p)


-- ---------------------------------
-- Parsing and dispatching TPDB TRSs
-- ---------------------------------

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


dispatchAProblem :: (MonadPlus m
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
                    ) => AProblem t trs -> Proof  (PrettyInfo, DotInfo) m ()

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



parseTRS :: (trs ~ NTRS id, id ~ Identifier String, Monad m) =>
             String -> m (AProblem (TermF id) trs)
parseTRS s = eitherM (runParser trsParser mempty "<input>" s)

trsParser :: TRS.TRSParser (AProblem (TermF (Identifier String)) (NTRS (Identifier String)))
trsParser = do
  Spec spec <- TRS.trsParser

  let allvars = Map.fromList (Set.toList(getVars spec) `zip` [0..])
      toTerm  = foldTerm toVar (Impure . fromSimple)
      toVar v = var' (Just v) (fromJust $ Map.lookup v allvars)

      spec'   = toTerm <$$> spec

      strategies = sort [s | Strategy s <- spec']

  let r   = [ l :-> r  | Rules rr <- spec', TRS.Rule (l TRS.:->  r) _ <- rr]
      r0  = [ mapTermSymbols IdFunction l :-> mapTermSymbols IdFunction r
                  | Rules rr <- spec', TRS.Rule (l TRS.:->= r) _ <- rr]
      dps = [markDPRule (mapTermSymbols IdFunction l :-> mapTermSymbols IdFunction r)
                  | Pairs rr <- spec', TRS.Rule (l TRS.:-> r) _ <- rr]
      r' = mapTermSymbols IdFunction <$$> r

      mkGoal = markDP . mapTermSymbols IdFunction

--      mkAbstractGoal :: Monad m => Term String -> m (Goal Id)
      mkAbstractGoal (Impure (Term id tt)) = do {tt' <- mapM mkMode tt; return (Goal (IdDP id) tt')}
      mkMode (Impure (Term "i" [])) = return G
      mkMode (Impure (Term "b" [])) = return G
      mkMode (Impure (Term "c" [])) = return G
      mkMode (Impure (Term "g" [])) = return G
      mkMode (Impure (Term "o" [])) = return V
      mkMode (Impure (Term "v" [])) = return V
      mkMode (Impure (Term "f" [])) = return V
      mkMode _                      = fail "not a mode"

  case (r0, dps, strategies) of
    ([], [], [])
        -> return $ ARewritingProblem (mkNewProblem Rewriting r)
    ([], [], [GoalStrategy g])
        -> return $ AGoalRewritingProblem (mkNewProblem (initialGoal [mkGoal g] Rewriting) r)

    ([], [], InnerMost:_)
        -> return $ AIRewritingProblem (mkNewProblem IRewriting r)
    ([], [], (GoalStrategy g : InnerMost : _))
        -> return $ AGoalIRewritingProblem (mkNewProblem (initialGoal [mkGoal g] IRewriting) r)

    ([], dps, [])
        -> return $ ARewritingProblem (mkDPProblem' Rewriting r' (tRS dps))
    ([], dps, [GoalStrategy g])
        -> return $ AGoalRewritingProblem (mkDPProblem' (initialGoal [mkGoal g] Rewriting) r' (tRS dps))

    ([], dps, InnerMost:_)
        -> return $ ARewritingProblem (mkDPProblem' Rewriting r' (tRS dps))
    ([], dps, GoalStrategy g:InnerMost:_)
        -> return $ AGoalIRewritingProblem (mkDPProblem' (initialGoal [mkGoal g] IRewriting) r' (tRS dps))

    (r0, [], [])
        -> return $ ARelativeRewritingProblem (mkNewProblem (relative (tRS r0) Rewriting) r)
    (r0, [], InnerMost:_)
        -> return $ ARelativeIRewritingProblem (mkNewProblem (relative (tRS r0) IRewriting) r)

    (r0, [], [GoalStrategy g])
        -> return $ AGoalRelativeRewritingProblem (mkNewProblem (relative (tRS r0) (initialGoal [mkGoal g] Rewriting)) r)
    (r0, [], GoalStrategy g:InnerMost:_)
        -> return $ AGoalRelativeIRewritingProblem (mkNewProblem (relative (tRS r0) (initialGoal [mkGoal g] IRewriting)) r)

    ([], [], TRS.Narrowing:_)        -> return $ ANarrowingProblem (mkNewProblem Narrowing r)
    ([], [], ConstructorNarrowing:_) -> return $ ACNarrowingProblem (mkNewProblem CNarrowing r)

    ([], [], GoalStrategy g:TRS.Narrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalNarrowingProblem (mkNewProblem (narrowingGoal g') r)}
    ([], [], GoalStrategy g:ConstructorNarrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalCNarrowingProblem (mkNewProblem (cnarrowingGoal g') r)}

-- --------------------------
-- Parsing Prolog problems
-- --------------------------

instance Error ParseError

prologParser = do
  txt    <- getInput
  goals  <- eitherM $ mapM parseGoal $ catMaybes $ map f (lines txt)
  clauses<- Prolog.whiteSpace >> many Prolog.clause
  return (prologProblem (concat goals) (concat clauses))
  where
    f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
    f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
    f _ = Nothing


-- ------------
-- Debug stuff
-- ------------
#ifdef HOOD
instance Observable Mode where observer = observeBase
#endif
