{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
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

import MuTerm.Framework.Problem
import MuTerm.Framework.Problem.Types
import MuTerm.Framework.Processor
import MuTerm.Framework.Proof

import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr

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

instance ( MkProblem p (NarradarTRS t Var), IsDPProblem p
         , HasId t, Foldable t, Unify t
         , Ord (Term t Var), Pretty (t(Term t Var))
         , Traversable (Problem p), Pretty p
         , ICap t Var (p, NarradarTRS t Var)
         , IUsableRules t Var (p, NarradarTRS t Var, NarradarTRS t Var)
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
         ,IUsableRules t Var (p, NarradarTRS t Var, NarradarTRS t Var)
         ) => MkDPProblem (InitialGoal t p) (NarradarTRS t Var) where
  mapP f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapP f p)
  mkDPProblem (InitialGoal goals g p) = (initialGoalProblem goals g .) . mkDPProblem p

initialGoal gg = InitialGoal gg Nothing

initialGoalProblem :: ( HasId t, Unify t, Ord (Term t Var), Pretty (t(Term t Var))
                      , IsDPProblem typ, Traversable (Problem typ), Pretty typ
                      , ICap t Var (typ, NarradarTRS t Var)
                      , IUsableRules t Var (typ, NarradarTRS t Var, NarradarTRS t Var)
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

reachablePairs :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var)
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> [Rule t Var]
reachablePairs p@InitialGoalProblem{dgraph=dg@DGraph{..},..}
  = map (`lookupPair` dg)
        (flattenSCCs (map (sccs A.!) sccsInPath))
 where
   sccsInvolved = Set.fromList $ catMaybes $ [ sccFor n dg
                                                   | p <- rules (getP p)
                                                   , Just n <- [lookupNode p dg]]
   initialSccs  = Set.fromList [ n | p <- initialPairsG
                                   , Just n <- [sccFor p dg]
                               ]

   sccsInPath   = toList $ unEmbed $ do
                    from <- embed initialSccs
                    to   <- embed sccsInvolved
                    embed $ nodesInPathNaive sccGraph from to

reachableRules :: (Ord(Term t Var), HasId t, Foldable t
                  ,IsDPProblem base, Traversable (Problem base)
                  ,IUsableRules t Var (Problem base (NarradarTRS t Var))
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> NarradarTRS t Var

reachableRules p = getR $ iUsableRules (baseProblem p) (rhs <$> reachablePairs p)

-- ---------
-- Instances
-- ---------

-- Functor

instance Functor (Problem p) => Functor (Problem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

-- Data.Term

instance (HasSignature (Problem p trs)) => HasSignature (Problem (InitialGoal id p) trs) where
  type SignatureId (Problem (InitialGoal id p) trs) = SignatureId (Problem p trs)
  getSignature = getSignature . baseProblem

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

-- Lifting Processors

liftProcessor :: ( Processor info tag (Problem base trs) (Problem base trs)
                 , Info info (Problem base trs), MonadPlus m
                 )=> tag -> Problem (InitialGoal t base) trs -> Proof info m (Problem (InitialGoal t base) trs)

liftProcessor tag p@InitialGoalProblem{..} = do
      p' <- apply tag baseProblem
      return p{baseProblem = p' `asTypeOf` baseProblem}


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
         ,IUsableRules t Var (p, trs, trs)
         ,IUsableRules t Var (IRewriting, trs, trs)
         ) =>
          IUsableRules t Var (InitialGoal t p, NarradarTRS t Var, NarradarTRS t Var)
  where
    iUsableRulesVarM (it@(InitialGoal _ _ p), trs, dps) v = do
      let the_problem = mkDPProblem it trs dps
      (_,reachableRules,_) <- iUsableRulesM (IRewriting, trs, dps) (rhs <$> reachablePairs the_problem)
      iUsableRulesVarM (p, reachableRules, dps) v
    iUsableRulesM (it@(InitialGoal _ _ p), trs, dps) tt = do
      let the_problem = mkDPProblem it trs dps
      (_,reachableRules,_) <- iUsableRulesM (IRewriting, trs, dps) (rhs <$> reachablePairs the_problem)
      pprTrace( text "The reachable rules are:" <+> pPrint reachableRules) (return ())
      (_,trs',_)           <- iUsableRulesM (p, reachableRules, dps) tt
      return (it, trs', dps)

-- Other Narradar instances


instance (trs ~ NTRS id
         ,MkDPProblem typ trs, Pretty typ, Traversable (Problem typ)
         ,Pretty id, Ord id, DPSymbol id
         ,NUsableRules id (typ, trs, trs)
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
                        ,initialPairsG :: [Vertex]      -- Indexes for the pairs Array
                        ,graph    :: Graph
                        ,sccs     :: Array Int (SCC Vertex)
                        ,sccsMap  :: Array Vertex (Maybe Int)
                        ,sccGraph :: Graph}

deriving instance Show a => Show (SCC a)
instance Pretty a => Pretty (DGraphF a) where
  pPrint DGraph{..} = text "DGraphF" <> brackets(vcat [text "pairs =" <+> pPrint (elems pairs)
                                                      ,text "pairsMap =" <+> pPrint pairsMap
                                                      ,text "initialPairs = " <+> pPrint initialPairsG
                                                      ,text "graph =" <+> text (show graph)
                                                      ,text "sccs =" <+> text (show sccs)
                                                      ,text "sccsMap =" <+> pPrint (elems sccsMap)
                                                      ,text "sccGraph =" <+> text (show sccGraph)])

mkDGraph :: ( IsDPProblem typ, Traversable (Problem typ), Pretty typ
            , HasId t, Unify t, Ord v, Pretty v, Enum v
            , Ord (Term t v), Pretty (t(Term t v))
            , ICap t v (typ, NarradarTRS t v)
            , IUsableRules t v (typ, NarradarTRS t v, NarradarTRS t v)
            ) => Problem typ (NarradarTRS t v) -> [Term t v] -> DGraph t v

mkDGraph p@(getP -> DPTRS _ gr _ _) gg = mkDGraph' (getProblemType p) (getR p) (getP p) gg gr
mkDGraph p gg = mkDGraph' (getProblemType p) (getR p) (getP p) gg (getEDG p)

mkDGraph' :: ( IsDPProblem typ, Traversable (Problem typ), Pretty typ, Pretty trs
            , HasId t, Unify t, Ord (Term t v), Ord v, Pretty v, Enum v, Pretty (t(Term t v))
            , ICap t v (typ, trs)
            , HasRules t v trs
            ) => typ -> trs -> trs -> [Term t v] -> Graph -> DGraph t v
mkDGraph' typ trs (rules -> dps) goals graph0 = runIcap (rules trs ++ dps) $ do
  let dd  = listArray (0, length dps - 1) dps
      p   = (typ,trs)

  -- List of indexes for graph0
  initialPairs0 <- liftM snub $ runListT $ do
                     (i,s :-> t) <- liftL (zip [0..] dps)
                     g           <- liftL goals
                     g'          <- lift (getFresh g >>= icap p)
                     guard(g' `unifies` s)
                     return i

  let -- list of indexes for graph0
      reachablePairs = Set.fromList $ concatMap (reachable graph0) initialPairs0

      -- list of indexes for graph
      pairs     = listArray (0,Set.size reachablePairs - 1)
                        [ dd A.! i | i <- Set.toList reachablePairs]

      pairsMap  = Map.fromList (zip (toList (elems pairs)) [0..])

      -- mapping index[graph0] -> index[graph] and viceversa
      reindexMap = array (0, length dps - 1)  (zip [0..length dps - 1] (repeat (-1)) ++
                                               zip (toList reachablePairs) [0..])
      reindex    = (reindexMap A.!)
      reindexInv = (array (bounds graph)  (zip [0..] (toList reachablePairs)) A.!)

      -- The graph we actually store, containing only reachable pairs
      graph     = buildG (0, Set.size reachablePairs - 1)
                         [ ( reindex v1, reindex v2 )
                         | e@(v1,v2) <- edges graph0
                         , v1 `Set.member` reachablePairs
                         , v2 `Set.member` reachablePairs]

      -- The actual initial pairs
      initialPairsG = map reindex initialPairs0

      -- A list of tuples (ix, scc, edges)
      sccGraphNodes = SCC.sccGraph graph
      ixes      = [ ix | (_,ix,_) <- sccGraphNodes ]
      sccGraph  = case ixes of
                    [] -> emptyArray
                    _  -> buildG (minimum ixes, maximum ixes)
                         [ (n1,n2) | (_, n1, nn) <- sccGraphNodes
                                   , n2 <- nn]
      sccs      = case ixes of
                    [] -> emptyArray
                    _  -> array (minimum ixes, maximum ixes)
                                 [ (ix, scc) | (scc,ix,_) <- sccGraphNodes]

      -- The scc for every node, with indexes from graph0
      sccsMap    = array (bounds graph0) (zip [0..length dps - 1] (repeat Nothing) ++
                                         [ (reindexInv n, Just ix) | (scc,ix,_) <- sccGraphNodes
                                                                   , n <- flattenSCC scc])
      the_dgraph = DGraph {..}


  pprTrace (text "Computing the dgraph for problem" <+> pPrint (typ, trs, dps) $$
            text "The initial pairs are:" <+> pPrint initialPairs0 $$
            text "where the EDG is:" <+> text (show graph0) $$
            text "The final graph stored is:" <+> text (show graph) $$
            text "where the mapping used for the nodes is" <+> pPrint (assocs reindexMap) $$
            text "and the final initial pairs are:" <+> pPrint initialPairsG
           ) $

  -- The index stored for a pair is within the range of the pairs array
   assert (all (inRange (bounds pairs)) (Map.elems pairsMap)) $
  -- The scc index stored for a pair is within the range of the sccs array
   assert (all (maybe True (inRange (bounds sccs))) (elems sccsMap)) $

   return the_dgraph

  where liftL = ListT . return

insertDGraph p@InitialGoalProblem{..} (rules -> newdps)
    = mkDGraph' (getProblemType baseProblem) (getR p) dps' goals graph'
  where
    dps'   = tRS(elems (pairs dgraph) ++ newdps)
    graph' = getEDG (setP dps' baseProblem)

-- TODO This is doing far more work than necessary
expandDGraph p@InitialGoalProblem{dgraph=dg@DGraph{..},..} olddp (rules -> newdps)
   | Nothing <- Map.lookup olddp pairsMap = dg
   | Just i  <- Map.lookup olddp pairsMap
   , dps'    <- tRS([pairs A.! j | j <- range (bounds pairs), j /= i] ++ newdps)
   , graph'  <- getEDG (setP dps' baseProblem)

   = mkDGraph' (getProblemType baseProblem) (getR p) dps' goals graph'



instance Ord a => Suitable DGraphF a where
  data Constraints DGraphF a = Ord a => DGraphConstraints
  constraints _ = DGraphConstraints

instance R.RFunctor DGraphF where
  fmap f x@DGraph{..} = withResConstraints $ \DGraphConstraints ->
                        DGraph{pairs = fmap f pairs, pairsMap = Map.mapKeys f pairsMap,..}

lookupNode p dg = Map.lookup p (pairsMap dg)

lookupPair n dg = pairs dg A.! n

sccFor n dg = sccsMap dg A.! n

dreachablePairs DGraph{..} = Set.fromList $ A.elems pairs

dinitialPairs g = map (pairs g A.!) (initialPairsG g)


nodesInPath :: DGraphF a -> Vertex -> Vertex -> Set Vertex
-- TODO Implement as a BF traversal on the graph, modified to accumulate the
--      set of possible predecessors instead of the direct one
nodesInPath dg@DGraph{..} from to
    | Just from' <- sccFor from dg
    , Just to'   <- sccFor to   dg
    , sccsInPath <- Set.intersection (Set.fromList $ reachable sccGraph from')
                                     (Set.fromList $ reachable (transposeG sccGraph) to')
    = Set.fromList (flattenSCCs [sccs A.! i | i <- Set.toList sccsInPath])

    | otherwise = Set.empty


nodesInPathNaive g from to = Set.intersection (Set.fromList $ reachable g from)
                                                  (Set.fromList $ reachable g' to)
  where g' = transposeG g
