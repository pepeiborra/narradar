{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs, TypeFamilies #-}

module Narradar.Types ( module Narradar.Framework
                      , module Narradar.Constraints.Unify
                      , module Narradar.Types
                      , module Narradar.Types.TRS
                      , module Narradar.Types.Problem
                      , module Narradar.Types.Problem.Rewriting
                      , module Narradar.Types.Problem.QRewriting
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
                      , Hashable, Lattice
                      , AF_, simpleHeu, bestHeu, innermost
                      ) where

import           Control.Applicative                  hiding (Alternative(..), many, optional)
import           Control.Arrow                        ((>>>))
import           Control.Monad                        (MonadPlus(..), (>=>), when)
import           Control.Monad.Trans                  (lift, liftIO)
import           Control.Monad.Error                  (runErrorT)
import           Data.ByteString.Char8                (ByteString, pack)
import           Data.List                            (maximumBy, sort, isSuffixOf)
import           Data.Hashable
import           Data.Maybe
import           Data.Monoid
import           Data.Suitable
import qualified Data.Map                             as Map
import qualified Data.Set                             as Set
import           Data.Traversable                     as T
import           Data.Typeable
import           Lattice                              (Lattice)
import           Text.ParserCombinators.Parsec
import qualified TRSParser                            as TRS
import qualified TRSTypes                             as TRS
import           TRSTypes                             hiding (Id, Rule, Term, TermF, Narrowing, Other, SimpleRuleF(..))
import           Prelude                              as P hiding (mapM, pi, sum)


import           MuTerm.Framework.DotRep
import           MuTerm.Framework.Strategy
import           MuTerm.Framework.Output

import qualified Data.Term.Family as Family

import           Narradar.Constraints.Unify
import           Narradar.Types.ArgumentFiltering     (AF_, simpleHeu, bestHeu, innermost)
import           Narradar.Types.DPIdentifiers         hiding (ArityId(..), StringId)
import           Narradar.Types.PrologIdentifiers
import           Narradar.Types.Labellings
import           Narradar.Types.Goal
import           Narradar.Types.Problem
import           Narradar.Types.Problem.Rewriting     hiding (m,dd,rr)
import           Narradar.Types.Problem.QRewriting    hiding (m,dd,rr)
import           Narradar.Types.Problem.Narrowing     hiding (baseProblem)
import           Narradar.Types.Problem.NarrowingGen  hiding (baseProblem, baseFramework)
import           Narradar.Types.Problem.NarrowingGoal hiding (baseProblem, goal)
import           Narradar.Types.Problem.Prolog
import           Narradar.Types.Problem.Relative      hiding (baseProblem, baseFramework)
import           Narradar.Types.Problem.InitialGoal   hiding (baseProblem, baseFramework, goals)
import           Narradar.Types.Problem.Infinitary    hiding (pi, baseProblem, baseFramework, pi_PType, heuristic)
import           Narradar.Types.TRS
import           Narradar.Types.Term
import           Narradar.Types.Var
import qualified Narradar.Types.Var                   as Narradar
import           Narradar.Utils
import           Narradar.Framework
import           Narradar.Framework.Ppr               as Ppr


import qualified TPDB.Data                            as TPDB
import qualified TPDB.XTC.Read                        as TPDB
import           Text.XML.HXT.Arrow.XmlState          ( runX )
import           Text.XML.HXT.Arrow.ReadDocument      ( readString )

import           Debug.Hoed.Observe

import           Prelude                              as P hiding (sum, pi, mapM)
import           Prelude.Extras

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

narradarParse x = narradarParseO nilObserver x
narradarParseO o name input
  | ".xml" `isSuffixOf` name = do
      e_p <- parseXMLO o input
      case e_p of
       Right p -> do
         writeFile (name ++ ".trs") (show $ pprAProblem p)
       Left  _ -> return ()
      return e_p
  | otherwise =
    return $
    let
       results = map (\p -> runParser p mempty name input)
                     [trsParserO o, APrologProblem <$> prologParser]
    in case results of
         [Right x, _] -> Right x
         [_, Right x] -> Right x
         [Left e1 , Left e2] -> Left $ bestError [e1,e2]

bestError :: [ParseError] -> String
bestError = show . maximumBy (compare `on` errorPos)
 where on cmp f x y = f x `cmp` f y

-- ---------------------------------
-- Parsing and dispatching TPDB TRSs
-- ---------------------------------
newtype PrettyDotF a = PrettyDotF a deriving (Functor, Pretty, DotRep, Generic, Generic1, Typeable)
instance Applicative PrettyDotF where
  pure = PrettyDotF
  PrettyDotF f <*> PrettyDotF a = PrettyDotF (f a)

data instance Constraints PrettyDotF a = (Pretty a, DotRep a, Observable a) => PrettyDotConstraint
instance (Pretty a, DotRep a, Observable a) => Suitable PrettyDotF a where constraints = PrettyDotConstraint

instance Observable1 PrettyDotF

instance Pretty (SomeInfo PrettyDotF) where
  pPrint (SomeInfo p) = withConstraintsOf p $ \PrettyDotConstraint -> pPrint p
instance DotRep (SomeInfo PrettyDotF) where
  dot (SomeInfo p) = withConstraintsOf p $ \PrettyDotConstraint -> dot p
  dotSimple (SomeInfo p) = withConstraintsOf p $ \PrettyDotConstraint -> dotSimple p
instance Observable(SomeInfo PrettyDotF) where
  observer (SomeInfo p) = withConstraintsOf p $ \PrettyDotConstraint -> SomeInfo . observer1 p

instance Show (SomeInfo PrettyDotF) where
  show = show . pPrint

instance Eq1 PrettyDotF where
  PrettyDotF a ==# PrettyDotF b = a == b

instance Ord1 PrettyDotF where
  PrettyDotF a `compare1` PrettyDotF b = compare a b

class Dispatch thing where
    dispatch :: (Traversable m, MonadPlus m, IsMZero m, Observable1 m) => thing -> Proof (PrettyDotF) m Final

mkDispatcher :: Monad m => (a -> Proof info m b) ->  a -> Proof info m Final
mkDispatcher f =  f >=> final

data AProblem t trs where
    ARewritingProblem              :: Problem Rewriting trs  -> AProblem t trs
    AIRewritingProblem             :: Problem IRewriting trs -> AProblem t trs
    AQRewritingProblem             :: Problem (QRewriting (Family.TermF trs)) trs -> AProblem t trs
    ANarrowingProblem              :: Problem Narrowing trs  -> AProblem t trs
    ACNarrowingProblem             :: Problem CNarrowing trs -> AProblem t trs
    ARelativeRewritingProblem      :: Problem (Relative trs Rewriting) trs -> AProblem t trs
    ARelativeIRewritingProblem     :: Problem (Relative trs IRewriting) trs -> AProblem t trs
    AGoalRelativeRewritingProblem  :: Problem (Relative trs (InitialGoal t Rewriting)) trs  -> AProblem t trs
    AGoalRelativeIRewritingProblem :: Problem (Relative trs (InitialGoal t IRewriting)) trs -> AProblem t trs
    AGoalRewritingProblem          :: Problem (InitialGoal t Rewriting) trs  -> AProblem t trs
    AGoalIRewritingProblem         :: Problem (InitialGoal t IRewriting) trs -> AProblem t trs
--    AGoalNarrowingProblem          :: Problem (NarrowingGoal (TermId t)) trs -> AProblem t trs
    AGoalNarrowingProblem          :: Problem (InitialGoal t Narrowing) trs -> AProblem t trs
    AGoalCNarrowingProblem         :: Problem (InitialGoal t INarrowing) trs -> AProblem t trs
--    AGoalCNarrowingProblem         :: Problem (CNarrowingGoal (TermId t)) trs -> AProblem t trs
    APrologProblem                 :: PrologProblem -> AProblem t trs
--    AGoalNarrowingRelativeRewritingProblem :: Problem (Relative trs NarrowingGoal (TermId t)) trs -> AProblem t trs

instance Observable1 (AProblem t) where observer1 = observeOpaque "A problem"

pprAProblem (ARewritingProblem  p) = pprTPDB $ setP (tRS []) p
pprAProblem (AIRewritingProblem p) = pprTPDB $ setP (tRS []) p
pprAProblem (ARelativeRewritingProblem p) = pprTPDB $ setP (tRS [])  p
pprAProblem (ARelativeIRewritingProblem p) = pprTPDB $ setP (tRS []) p

dispatchAProblem :: (Traversable m, MonadPlus m, IsMZero m, Observable1 m
                    ,Dispatch (Problem Rewriting  trs)
                    ,Dispatch (Problem (QRewriting (Family.TermF trs))  trs)
                    ,Dispatch (Problem IRewriting trs)
                    ,Dispatch (Problem (InitialGoal t Rewriting) trs)
                    ,Dispatch (Problem (InitialGoal t IRewriting) trs)
                    ,Dispatch (Problem (Relative  trs (InitialGoal t Rewriting))  trs)
                    ,Dispatch (Problem (Relative  trs (InitialGoal t IRewriting))  trs)
                    ,Dispatch (Problem (Relative  trs Rewriting)  trs)
                    ,Dispatch (Problem (Relative  trs IRewriting)  trs)
                    ,Dispatch (Problem Narrowing  trs)
                    ,Dispatch (Problem CNarrowing trs)
                    ,Dispatch (Problem (InitialGoal t Narrowing) trs)
                    ,Dispatch (Problem (InitialGoal t INarrowing) trs)
                    ,Dispatch PrologProblem
                    ) => AProblem t trs -> Proof PrettyDotF m Final

dispatchAProblem (ARewritingProblem p)         = dispatch p
dispatchAProblem (AIRewritingProblem p)        = dispatch p
dispatchAProblem (AQRewritingProblem p)        = dispatch p
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

parseXML :: String -> IO (Either String (AProblem (TermF Id) (NTRS Id)))
parseXML = parseXMLO nilObserver
parseXMLO obs@(O o oo) inp = runErrorT $ do
  problems <- lift $ runX (readString [] inp >>> TPDB.getProblem)
  case problems of
   [ p@TPDB.Problem { TPDB.type_ = TPDB.Termination } ] ->
     let r  = map convertRule (TPDB.strict_rules $ TPDB.trs p)
         r0 = map convertRule (TPDB.weak_rules   $ TPDB.trs p)
     in mkAProblem obs r A r0 Nothing []
   []  -> fail "parse XML failed."
   [_] -> fail "Can only do termination problems."
   _   -> fail "Can only do one problem at once."
  where
   convertRule (l, r) = convertTerm l :-> convertTerm r
   convertTerm (TPDB.Var  (TPDB.Identifier hash name arity)      ) =
     return (Narradar.Var (Just name) hash)
   convertTerm (TPDB.Node (TPDB.Identifier hash name arity) nodes) =
     Impure (Term (ArityId (pack name) arity) (map convertTerm nodes))

trsParser = trsParserO nilObserver
trsParserO :: Observer -> TRS.TRSParser (AProblem (TermF Id) (NTRS Id))
trsParserO obs@(O o oo) = do
  Spec spec <- TRS.trsParser

  let allvars = Map.fromList (Set.toList(getVars spec) `zip` [0..])
      toTerm  = foldTerm toVar (wrap . fromSimple)
      toVar v = var' (Just v) (fromJust $ Map.lookup v allvars)

      spec'   = toTerm <$$> spec

      strategies = sort [s | Strategy s <- spec']
      minimality = if TRSTypes.Any (Just "MINIMALITY") [] `elem` spec
                    then M
                    else A

  let r   = [ l :-> r  | Rules rr <- spec', TRS.Rule (l TRS.:->  r) _ <- rr]
      r0  = [ l :-> r  | Rules rr <- spec', TRS.Rule (l TRS.:->= r) _ <- rr]
      dps = if null [()|Pairs{}<-spec]
              then Nothing
              else Just [markDPRule (mapTermSymbols IdFunction l :-> mapTermSymbols IdFunction r)
                             | Pairs rr <- spec', TRS.Rule (l TRS.:-> r) _ <- rr]

  mkAProblem obs r minimality r0 dps strategies

mkAProblem (O o oo) r minimality r0_ dps strategies =
  let
      r' = mkTRS (mapTermSymbols IdFunction <$$> r)
      r0 =        mapTermSymbols IdFunction <$$> r0_
      mkGoal = Concrete . markDP . mapTermSymbols IdFunction

--      mkAbstractGoal :: Monad m => Term String -> m (Goal Id)
--      mkAbstractGoal (Impure (Term id tt)) = do {tt' <- mapM mkMode tt; return (Goal (IdDP id) tt')}
      mkAbstractGoal (Impure (Term id tt)) = do {tt' <- mapM mkMode tt;
                                                 return (Abstract $ term (IdDP id) (map return tt'))}
      mkMode (Impure (Term (the_id -> "i") [])) = return G
      mkMode (Impure (Term (the_id -> "b") [])) = return G
      mkMode (Impure (Term (the_id -> "c") [])) = return G
      mkMode (Impure (Term (the_id -> "g") [])) = return G
      mkMode (Impure (Term (the_id -> "o") [])) = return V
      mkMode (Impure (Term (the_id -> "v") [])) = return V
      mkMode (Impure (Term (the_id -> "f") [])) = return V
      mkMode _                      = fail "parsing the abstract goal"

  in
  case (r0, dps, strategies) of
    ([], Nothing, [])  -> return $ ARewritingProblem (oo "mkNewProblem" mkNewProblemO rewriting r)
    ([], Nothing, TRS.Narrowing:_)        -> return $ ANarrowingProblem (oo "mkNewProblem" mkNewProblemO narrowing r)
    ([], Nothing, ConstructorNarrowing:_) -> return $ ACNarrowingProblem (oo "mkNewProblem" mkNewProblemO cnarrowing r)
    ([], Nothing, InnerMost:TRS.Narrowing:_)  -> return $ ACNarrowingProblem (oo "mkNewProblem" mkNewProblemO cnarrowing r)

    ([], Nothing, [GoalStrategy g])
      -> return $ AGoalRewritingProblem (oo "mkNewProblem" mkNewProblemO (initialGoal [mkGoal g] rewriting) r)

    ([], Nothing, InnerMost:_)
        -> return $ AIRewritingProblem (oo "mkNewProblem" mkNewProblemO irewriting r)
    ([], Nothing, GoalStrategy g:TRS.Narrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalNarrowingProblem (oo "mkNewProblem" mkNewProblemO (initialGoal [g'] narrowing) r)}
--    (r0, Nothing, GoalStrategy g:TRS.Narrowing:_)
--        -> do {g' <- mkAbstractGoal g; return $ AGoalNarrowingRelativeRewritingProblem
--                                                (oo "mkNewProblem" mkNewProblemO (relative (tRS r0) (narrowingGoal g')) r)}
    ([], Nothing, GoalStrategy g:ConstructorNarrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalCNarrowingProblem (oo "mkNewProblem" mkNewProblemO (initialGoal [g'] cnarrowing) r)}
    ([], Nothing, GoalStrategy g:InnerMost:TRS.Narrowing:_)
        -> do {g' <- mkAbstractGoal g; return $ AGoalCNarrowingProblem (oo "mkNewProblem" mkNewProblemO (initialGoal [g'] cnarrowing) r)}
    ([], Nothing, (GoalStrategy g : InnerMost : _))
        -> return $ AGoalIRewritingProblem (oo "mkNewProblem" mkNewProblemO (initialGoal [mkGoal g] irewriting) r)
    ([], Nothing, (TRS.Q q : _))
      -> return $ AQRewritingProblem (oo "mkNewProblem" mkNewProblemO (qRewritingO nilObserver (mapTermSymbols IdFunction <$> q) minimality) r)
    ([], Just dps, (TRS.Q q : _))
        -> return $ AQRewritingProblem (mkDPProblem (qRewritingO nilObserver (mapTermSymbols IdFunction <$> q) minimality) r' (mkTRS dps))
    ([], Just dps, [])
        -> return $ ARewritingProblem (setMinimality minimality $ mkDPProblem rewriting r' (mkTRS dps))

    ([], Just dps, [GoalStrategy g])
        -> return $ AGoalRewritingProblem (setMinimality minimality $ mkDPProblem (initialGoal [mkGoal g] rewriting) r' (tRS dps))

    ([], Just dps, GoalStrategy g:TRS.Narrowing:_)
        -> do {g' <- mkAbstractGoal g;
               return $ AGoalNarrowingProblem (setMinimality minimality $ mkDPProblem (initialGoal [g'] narrowing) r' (tRS dps))}

    ([], Just dps, InnerMost:_)
        -> return $ AIRewritingProblem (setMinimality minimality $ mkDPProblem irewriting r' (tRS dps))
    ([], Just dps, GoalStrategy g:InnerMost:_)
        -> return $ AGoalIRewritingProblem (setMinimality minimality $ mkDPProblem (initialGoal [mkGoal g] irewriting) r' (tRS dps))

    (r0, Nothing, [])
        -> return $ ARelativeRewritingProblem (oo "mkNewProblem" mkNewProblemO (relative (tRS r0) rewriting) r)
    (r0, Nothing, InnerMost:_)
        -> return $ ARelativeIRewritingProblem (oo "mkNewProblem" mkNewProblemO (relative (tRS r0) irewriting) r)


    (r0, Nothing, [GoalStrategy g])
        -> return $ AGoalRelativeRewritingProblem (oo "mkNewProblem" mkNewProblemO (relative (tRS r0) (initialGoal [mkGoal g] rewriting)) r)
    (r0, Nothing, GoalStrategy g:InnerMost:_)
        -> return $ AGoalRelativeIRewritingProblem (oo "mkNewProblem" mkNewProblemO (relative (tRS r0) (initialGoal [mkGoal g] irewriting)) r)


    (r0, Just dps, [])
        -> return $ ARelativeRewritingProblem (setMinimality minimality $
                                               mkDPProblem (relative (tRS r0) rewriting) r' (tRS dps))

    (r0, Just dps, InnerMost:_)
        -> return $ ARelativeIRewritingProblem (setMinimality minimality $
                                                mkDPProblem (relative (tRS r0) irewriting) r' (tRS dps))
    (r0, Just dps, [GoalStrategy g])
        -> return $ AGoalRelativeRewritingProblem
                  $ setMinimality A
                  $ mkDPProblem (relative (tRS r0) (initialGoal [mkGoal g] rewriting)) r' (mkTRS dps)

    (r0, Just dps, GoalStrategy g:InnerMost:_)
        -> return $ AGoalRelativeIRewritingProblem
                  $ mkDPProblem (relative (tRS r0) (initialGoal [mkGoal g] irewriting)) r' (mkTRS dps)

    _   -> fail "Invalid combination of rules, pairs and/or goals"
