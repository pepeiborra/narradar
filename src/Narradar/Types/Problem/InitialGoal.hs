{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}

module Narradar.Types.Problem.InitialGoal where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Control.Monad.List
import qualified Control.RMonad as R
import Control.RMonad.AsMonad (embed, unEmbed)
import Data.Bifunctor
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Array as A
import Data.Graph as G
import Data.Graph.SCC as SCC
import Data.Maybe
import Data.Monoid
import Data.Strict ( Pair(..) )
import Data.Suitable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Text.XHtml (HTML(..), theclass, (+++))

import Data.Term hiding ((!))
import Data.Term.Rules

import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Var
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils

import Prelude hiding (pi)

data InitialGoal t p = InitialGoal
    { goals_PType     :: [Term t Var]
    , dgraph_PType    :: Maybe (DGraph t Var)
    , baseProblemType :: p}

instance (Eq p, Eq (Term t Var)) => Eq (InitialGoal t p) where
    p0 == p1 = (goals_PType p0, baseProblemType p0) == (goals_PType p1, baseProblemType p1)

instance (Ord p, Ord (Term t Var)) => Ord (InitialGoal t p) where
    compare p0 p1 = compare (goals_PType p0, baseProblemType p0) (goals_PType p1, baseProblemType p1)

instance (Show p, Show (Term t Var)) => Show (InitialGoal t p) where
    show p0 = show (goals_PType p0, baseProblemType p0)

instance Functor (InitialGoal t) where
    fmap f (InitialGoal goals dg p) = InitialGoal goals dg (f p)

instance (IsProblem p, HasId t, Foldable t) => IsProblem (InitialGoal t p) where
  data Problem (InitialGoal t p) a = InitialGoalProblem { goals       :: [Term t Var]
                                                        , dgraph      :: DGraph t Var
                                                        , baseProblem :: Problem p a}
  getProblemType (InitialGoalProblem goals g p) = InitialGoal goals (Just g) (getProblemType p)
  getR   (InitialGoalProblem _     _ p) = getR p

instance ( MkDPProblem p (NarradarTRS t Var)
         , HasId t, Foldable t, Unify t
         , Ord (Term t Var), Pretty (t(Term t Var))
         , Traversable (Problem p), Pretty p
         , ICap t Var (p, NarradarTRS t Var)
         , IUsableRules t Var p (NarradarTRS t Var)
         ) =>
     MkProblem (InitialGoal t p) (NarradarTRS t Var)
 where
  mkProblem (InitialGoal gg gr p) rr = initialGoalProblem gg gr (mkProblem p rr)
  mapR f (InitialGoalProblem goals g@DGraph{..} p) = initialGoalProblem goals Nothing (mapR f p)

instance (IsDPProblem p, HasId t, Foldable t) => IsDPProblem (InitialGoal t p) where
  getP   (InitialGoalProblem _     _ p) = getP p

instance (HasId t, Unify t, Foldable t, MkDPProblem p (NarradarTRS t Var), Pretty p
         ,Pretty(t(Term t Var)), Ord (Term t Var), Traversable (Problem p)
         ,ICap t Var (p, NarradarTRS t Var)
         ,MkDPProblem p (NarradarTRS t Var)
         ,IUsableRules t Var p (NarradarTRS t Var)
         ) => MkDPProblem (InitialGoal t p) (NarradarTRS t Var) where
  mapP f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapP f p)
  mkDPProblem (InitialGoal goals g p) = (initialGoalProblem goals g .) . mkDPProblem p

instance FrameworkExtension (InitialGoal t) where
  getBaseFramework = baseProblemType
  getBaseProblem   = baseProblem
  setBaseProblem p0 p = p{baseProblem=p0}

initialGoal gg = InitialGoal gg Nothing

initialGoalProblem :: ( HasId t, Unify t, Ord (Term t Var), Pretty (t(Term t Var))
                      , MkDPProblem typ (NarradarTRS t Var)
                      , Traversable (Problem typ), Pretty typ
                      , ICap t Var (typ, NarradarTRS t Var)
                      , IUsableRules t Var typ (NarradarTRS t Var)
                      ) =>
                      [Term t Var]
                   -> Maybe(DGraph t Var)
                   -> Problem typ (NarradarTRS t Var) -> Problem (InitialGoal t typ) (NarradarTRS t Var)

initialGoalProblem gg Nothing p = InitialGoalProblem gg (mkDGraph p gg) p
initialGoalProblem gg (Just dg) p = InitialGoalProblem gg dg p

updateInitialGoalProblem p p0 = p{baseProblem = p0}

-- ----------
-- Functions
-- ----------
{-# RULES "Set fromList/toList" forall x. Set.fromList(Set.toList x) = x #-}

initialPairs :: Unify t => Problem (InitialGoal t base) trs -> [Rule t Var]
initialPairs InitialGoalProblem{..} = dinitialPairs dgraph


-- | returns the vertexes in the DGraph which are in a path from an initial pair to the current P
involvedNodes :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var)
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> [Vertex]
involvedNodes p = involvedNodes' p (getP p)

-- | returns the vertexes in the DGraph which are in a path from an initial pair to a given TRS P
involvedNodes' :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var)
                  ,HasRules t Var trs
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> trs -> [Vertex]
involvedNodes' p@InitialGoalProblem{dgraph=dg@DGraph{..},..} pTRS
  = flattenSCCs (map (safeAt "involvedNodes" sccs) sccsInPath)
 where
   sccsInvolved = Set.fromList $ catMaybes $ [ sccFor n dg
                                                   | p <- rules pTRS
                                                   , Just n <- [lookupNode p dg]]
   initialSccs  = Set.fromList [ n | p0 <- toList initialPairsG
                                   , Just n <- [sccFor p0 dg]
                               ]

   sccsInPath   = toList $ unEmbed $ do
                    from <- embed initialSccs
                    to   <- embed sccsInvolved
                    embed $ nodesInPathNaive sccGraph from to


involvedPairs :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var)
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> [Rule t Var]
involvedPairs p@InitialGoalProblem{dgraph=dg@DGraph{..},..}
  = map (`lookupPair` dg) (snub(involvedNodes p ++ pairs ++ toList initialPairsG))
 where
   pairs = catMaybes(map (`lookupNode` dg) (rules $ getP p))

reachableUsableRules :: (Ord(Term t Var), HasId t, Foldable t
                  ,MkDPProblem base (NarradarTRS t Var), Traversable (Problem base)
                  ,IUsableRules t Var base (NarradarTRS t Var)
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> NarradarTRS t Var

reachableUsableRules p = getR $ iUsableRules (baseProblem p) (rhs <$> involvedPairs p)

-- ---------
-- Instances
-- ---------

-- Functor

instance Functor (Problem p) => Functor (Problem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

-- Data.Term

-- Output

instance Pretty p => Pretty (InitialGoal id p) where
    pPrint InitialGoal{..} = text "Initial Goal" <+> pPrint baseProblemType


instance (Pretty (Term t Var), Pretty (Problem base trs)) =>
    Pretty (Problem (InitialGoal t base) trs)
 where
  pPrint InitialGoalProblem{..} =
      pPrint baseProblem $$
      text "GOALS:" <+> pPrint goals


instance HTML p => HTML (InitialGoal id p) where
    toHtml InitialGoal{..} = toHtml "Initial goal " +++ baseProblemType

instance HTMLClass (InitialGoal id typ) where htmlClass _ = theclass "G0DP"


-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (InitialGoal id p, trs)
  where
    icap (InitialGoal{..},trs) = icap (baseProblemType,trs)

-- Usable Rules
{-
instance (HasId t, Foldable t, Unify t, Ord (Term t Var), Pretty (Term t Var)
         ,IsDPProblem p, Traversable (Problem p), Pretty p
         ,trs ~ NarradarTRS t Var
         ,MkDPProblem p trs
         ,IUsableRules t Var (Problem p trs)
         ) =>
          IUsableRules t Var (Problem (InitialGoal t p) (NarradarTRS t Var))
  where
    iUsableRulesVar p = iUsableRulesVar (baseProblem p)
    iUsableRulesM p tt = do
      (getR -> reachableRules) <- iUsableRulesM (baseProblem p) (rhs <$> reachablePairs p)
      (getR -> trs')           <- iUsableRulesM (setR reachableRules (baseProblem p)) tt
      return (setR trs' p)
-}
instance (HasId t, Foldable t, Unify t, Ord (t(Term t Var)), Pretty (t(Term t Var))
         ,IsDPProblem p, Traversable (Problem p), Pretty p
         ,trs ~ NarradarTRS t Var
         ,MkDPProblem p trs
         ,ICap t Var (p, trs)
         ,IUsableRules t Var p trs
         ) =>
          IUsableRules t Var (InitialGoal t p) trs
  where
    iUsableRulesVarM it@(InitialGoal _ _ p) trs dps v = do
      let the_problem = mkDPProblem it trs dps
      reachableRules <- iUsableRulesM irewriting trs dps (rhs <$> involvedPairs the_problem)
      iUsableRulesVarM p reachableRules dps v

    iUsableRulesM it@(InitialGoal _ _ p) trs dps tt = do
      let the_problem = mkDPProblem it trs dps
      reachableRules <- iUsableRulesM irewriting trs dps =<< getFresh (rhs <$> involvedPairs the_problem)
      pprTrace( text "The reachable rules are:" <+> pPrint reachableRules) (return ())
      iUsableRulesM p reachableRules dps tt


-- Other Narradar instances

instance (trs ~ NTRS id
         ,MkDPProblem typ trs, Pretty typ, Traversable (Problem typ)
         ,Pretty id, Ord id, DPSymbol id
         ,NUsableRules typ id
         ,NCap id (typ, trs)
         ,InsertDPairs typ (NTRS id)
         ) =>
  InsertDPairs (InitialGoal (TermF id) typ) (NTRS id)
 where
  insertDPairs p@InitialGoalProblem{dgraph=DGraph{..},..} newPairs
    = let base'   = insertDPairs baseProblem newPairs
          dgraph' = insertDGraph p newPairs
      in initialGoalProblem goals (Just dgraph') base'

-- -------------------------------
-- Dependency Graph data structure
-- -------------------------------
type DGraph t v = DGraphF (Rule t v)

data DGraphF a = DGraph {pairs    :: Array Int a
                        ,pairsMap :: Map a Int
                        ,initialPairsG   :: Set Vertex
                        ,reachablePairsG :: Set Vertex
                        ,fullgraph:: Graph
                        ,sccs     :: Array Int (SCC Vertex)
                        ,sccsMap  :: Array Vertex (Maybe Int)
                        ,sccGraph :: Graph}

deriving instance Show a => Show (SCC a)
instance Pretty a => Pretty (DGraphF a) where
  pPrint DGraph{..} = text "DGraphF" <> brackets(vcat [text "pairs =" <+> pPrint (elems pairs)
                                                      ,text "pairsMap =" <+> pPrint pairsMap
                                                      ,text "initial pairs = " <+> pPrint initialPairsG
                                                      ,text "reachable pairs = " <+> pPrint reachablePairsG
                                                      ,text "graph =" <+> text (show fullgraph)
                                                      ,text "sccs =" <+> text (show sccs)
                                                      ,text "sccsMap =" <+> pPrint (elems sccsMap)
                                                      ,text "sccGraph =" <+> text (show sccGraph)])

mkDGraph :: ( MkDPProblem typ (NarradarTRS t v)
            , Traversable (Problem typ), Pretty typ
            , HasId t, Unify t, Ord v, Pretty v, Enum v
            , Ord    (Term t v)
            , Pretty (Term t v)
            , Pretty (NarradarTRS t v)
            , ICap t v (typ, NarradarTRS t v)
            , IUsableRules t v typ (NarradarTRS t v)
            ) => Problem typ (NarradarTRS t v) -> [Term t v] -> DGraph t v

mkDGraph p@(getP -> DPTRS _ gr _ _) gg = mkDGraph' (getProblemType p) (getR p) (getP p) gg gr
mkDGraph p gg = mkDGraph' (getProblemType p) (getR p) (getP p) gg (getEDG p)

mkDGraph' :: ( IsDPProblem typ, Traversable (Problem typ), Pretty typ, Pretty trs
            , HasId t, Unify t, Ord (Term t v), Ord v, Pretty v, Enum v, Pretty (Term t v)
            , ICap t v (typ, trs)
            , HasRules t v trs
            ) => typ -> trs -> trs -> [Term t v] -> Graph -> DGraph t v
mkDGraph' typ trs (rules -> dps) goals fullgraph = runIcap (rules trs ++ dps) $ do
  let pairs    = listArray (0, length dps - 1) dps
      pairsMap = Map.fromList (dps `zip` [0..])
      p   = (typ,trs)

  -- List of indexes for fullgraph
  initialPairsG <- liftM Set.fromList $ runListT $ do
                     (i,s :-> t) <- liftL (zip [0..] dps)
                     g           <- liftL goals
                     g'          <- lift (getFresh g >>= icap p)
                     guard(g' `unifies` s)
                     return i

  let -- list of indexes for fullgraph
      reachablePairsG = Set.fromList $ concatMap (reachable fullgraph) (toList initialPairsG)

      -- A list of tuples (ix, scc, edges)
      sccGraphNodes = [ it | it@(flattenSCC -> nn,_,_) <-SCC.sccGraph fullgraph
                           , any (`Set.member` reachablePairsG) nn]

      sccsIx   = [ ix | (_,ix,_) <- sccGraphNodes]
      sccGraph  = case sccsIx of
                    [] -> emptyArray
                    _  -> buildG (minimum sccsIx, maximum sccsIx)
                         [ (n1,n2) | (_, n1, nn) <- sccGraphNodes
                                   , n2 <- nn]
      sccs      = case sccsIx of
                    [] -> emptyArray
                    _  -> array (minimum sccsIx, maximum sccsIx)
                                 [ (ix, scc) | (scc,ix,_) <- sccGraphNodes]

      -- The scc for every node, with indexes from fullgraph
      sccsMap    = array (bounds fullgraph) (zip [0..length dps - 1] (repeat Nothing) ++
                                         [ (n, Just ix) | (scc,ix,_) <- sccGraphNodes
                                                                   , n <- flattenSCC scc])
      the_dgraph = DGraph {..}


  pprTrace (text "Computing the dgraph for problem" <+> pPrint (typ, trs, dps) $$
            text "The initial pairs are:" <+> pPrint initialPairsG $$
            text "where the EDG is:" <+> text (show fullgraph)
--            text "The final graph stored is:" <+> text (show graph) $$
--            text "where the mapping used for the nodes is" <+> pPrint (assocs reindexMap) $$
--            text "and the final initial pairs are:" <+> pPrint initialPairsG
           ) $

  -- The index stored for a pair is within the range of the pairs array
--   assert (all (inRange (bounds pairs)) (Map.elems pairsMap)) $
  -- The scc index stored for a pair is within the range of the sccs array
   assert (all (maybe True (inRange (bounds sccs))) (elems sccsMap)) $
  -- No duplicate edges in the graph
   assert (noDuplicateEdges fullgraph) $
   return the_dgraph

  where liftL = ListT . return

insertDGraph p@InitialGoalProblem{..} (rules -> newdps)
    = mkDGraph' (getProblemType baseProblem) (getR p) dps' goals graph'
  where
    dps'   = tRS(elems (pairs dgraph) ++ newdps)
    graph' = getEDG (setP dps' baseProblem)

expandDGraph ::
      ( Unify t, HasId t
      , Pretty (t(Term t Var))
      , Ord    (Term t Var)
      , Traversable (Problem typ), Pretty typ
      , MkDPProblem typ (NarradarTRS t Var)
      , ICap t Var (typ, NarradarTRS t Var)
      , IUsableRules t Var typ (NarradarTRS t Var)
      ) =>
      Problem (InitialGoal t typ) (NarradarTRS t Var) -> Rule t Var -> [Rule t Var] -> DGraph t Var
-- TODO This is doing far more work than necessary
expandDGraph p@InitialGoalProblem{dgraph=dg@DGraph{..},..} olddp newdps
   | Nothing <- Map.lookup olddp pairsMap = dg
   | Just i  <- Map.lookup olddp pairsMap
   , dps'    <- tRS([ dp | (j,dp) <- assocs pairs, j /= i] ++ newdps)
   , graph'  <- getEDG (setP dps' baseProblem)

   = mkDGraph' (getProblemType baseProblem) (getR p) dps' goals graph'



instance Ord a => Suitable DGraphF a where
  data Constraints DGraphF a = Ord a => DGraphConstraints
  constraints _ = DGraphConstraints

instance R.RFunctor DGraphF where
  fmap f x@DGraph{..} = withResConstraints $ \DGraphConstraints ->
                        DGraph{pairs = fmap f pairs, pairsMap = Map.mapKeys f pairsMap,..}

lookupNode p dg = Map.lookup p (pairsMap dg)

lookupPair n dg = safeAt "lookupPair" (pairs dg) n

sccFor n dg = safeAt "sccFor" (sccsMap dg) n

dreachablePairs DGraph{..} = Set.fromList $ A.elems pairs

dinitialPairs g = map (safeAt "initialPairs" (pairs g)) (toList $ initialPairsG g)


nodesInPath :: DGraphF a -> Vertex -> Vertex -> Set Vertex
-- TODO Implement as a BF traversal on the graph, modified to accumulate the
--      set of possible predecessors instead of the direct one
nodesInPath dg@DGraph{..} from to
    | Just from' <- sccFor from dg
    , Just to'   <- sccFor to   dg
    , sccsInPath <- Set.intersection (Set.fromList $ reachable sccGraph from')
                                     (Set.fromList $ reachable (transposeG sccGraph) to')
    = Set.fromList (flattenSCCs [safeAt "nodesInPath" sccs i | i <- Set.toList sccsInPath])

    | otherwise = Set.empty


nodesInPathNaive g from to = Set.intersection (Set.fromList $ reachable g from)
                                              (Set.fromList $ reachable g' to)
  where g' = transposeG g
