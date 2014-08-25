{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{- LANGUAGE NoMonoLocalBinds -}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}

module Narradar.Types.Problem.InitialGoal where

import Control.Applicative
import Control.DeepSeq
import Control.DeepSeq.Extras
import Control.Exception (assert)
import Control.Monad.Identity
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
import Data.Monoid ( Monoid(..) )
import Data.Strict ( Pair(..) )
import Data.Suitable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable (Typeable)
import Text.XHtml (HTML(..), theclass, (+++))

import Data.Term hiding ((!), TermF, Var)
import qualified Data.Term.Family as Family
import Data.Term.Rules

import Narradar.Types.DPIdentifiers
import Narradar.Types.Goal
import Narradar.Types.Problem
import Narradar.Types.Problem.Rewriting
import Narradar.Types.Problem.Narrowing hiding (baseProblem)
import Narradar.Types.Problem.NarrowingGen hiding (baseProblem, baseFramework)
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Var
import Narradar.Framework
import Narradar.Framework.Constraints
import Narradar.Framework.Ppr
import Narradar.Utils

import qualified Narradar.Types.Problem.Narrowing as N

import Prelude hiding (pi)

import GHC.Generics (Generic)
import Debug.Hoed.Observe

data InitialGoal t p = InitialGoal
    { goals_PType     :: [CAGoal t]
    , dgraph_PType    :: Maybe (DGraph t Var)
    , baseFramework :: p}
  deriving (Generic, Typeable)

data CAGoalF c a = Concrete c
                 | Abstract a
  deriving (Eq, Ord, Show, Functor, Generic, Typeable)

type GoalTerm t = Term t Mode

type CAGoal t = CAGoalF (Term t Var) (GoalTerm t)

instance (Eq p, Eq (Term t Var), Eq (GoalTerm t)) => Eq (InitialGoal t p) where
    p0 == p1 = (goals_PType p0, baseFramework p0) == (goals_PType p1, baseFramework p1)

instance (Ord p, Ord (Term t Var), Ord (GoalTerm t)) => Ord (InitialGoal t p) where
    compare p0 p1 = compare (goals_PType p0, baseFramework p0) (goals_PType p1, baseFramework p1)

instance (Show p, Show (Term t Var), Show (GoalTerm t)) => Show (InitialGoal t p) where
    show p0 = show (goals_PType p0, baseFramework p0)

instance Functor (InitialGoal t) where
    fmap f (InitialGoal goals dg p) = InitialGoal goals dg (f p)

mapInitialGoal :: forall t t' p .
                  ( Functor t, Functor t', Foldable t', HasId1 t'
                  , Ord (Term t Var), Ord(Term t' Var)
                  , Observable1 t'
                  ) =>
                  (forall a. t a -> t' a) -> InitialGoal t p -> InitialGoal t' p
mapInitialGoal f (InitialGoal goals dg p) = InitialGoal goals' dg' p
      where
        goals' = map (bimap f' f') goals
        dg'    = mapDGraph f' <$> dg
        f'    :: forall a. Term t a -> Term t' a
        f'     = foldTerm return (Impure . f)

instance (IsProblem p, HasId1 t, Foldable t) => IsProblem (InitialGoal t p) where
  data Problem (InitialGoal t p) a = InitialGoalProblem { goals       :: [CAGoal t]
                                                        , dgraph      :: DGraph t Var
                                                        , baseProblem :: Problem p a}
                                     deriving (Generic)
  getFramework (InitialGoalProblem goals g p) = InitialGoal goals (Just g) (getFramework p)
  getR   (InitialGoalProblem _     _ p) = getR p

deriving instance (HasId1 t, Foldable t, Ord(Family.Id t), RemovePrologId(Family.Id t), Eq (Problem p a), Eq (Term t Mode), Ord(Term t Var)) => Eq (Problem (InitialGoal t p) a)
--  p1 == p2 = baseProblem p1 == baseProblem p2

deriving instance (HasId1 t, Foldable t, Ord(Family.Id t), RemovePrologId(Family.Id t), Ord (Problem p a), Ord (Term t Mode), Ord(Term t Var)) => Ord (Problem (InitialGoal t p) a)


instance (IsDPProblem p, HasId1 t, Foldable t) => IsDPProblem (InitialGoal t p) where
  getP   (InitialGoalProblem _     _ p) = getP p

instance ( t ~ f id, MapId f
         , FrameworkId id, DPSymbol id
         , FrameworkN p t Var
         , FrameworkN (InitialGoal t p) t Var
         ) =>
     MkProblem (InitialGoal t p) (NarradarTRS t Var)
 where
  mkProblemO o (InitialGoal gg gr p) rr = initialGoalProblem o gg gr (mkProblem p rr)
  mapRO o f p@(InitialGoalProblem goals dg _) = p'{dgraph = dg'}
   where
    p'     = dpTRSO o (runIdentity $ liftProblem (return . mapR f) p)
    dg'    = mkDGraphO o p' goals
  setR_uncheckedO o rr p = p{baseProblem = setR_uncheckedO o rr (baseProblem p)}

mkIGDPProblem ::
         (t ~ f id, MapId f
         ,v ~ Var
         ,FrameworkId id, DPSymbol id
         ,FrameworkN (InitialGoal t p) t v
         ,FrameworkN p t v
         ,Eq (GoalTerm t), Pretty (GoalTerm t)
         ) => Observer -> InitialGoal t p -> NarradarTRS t v -> NarradarTRS t v ->
              Problem (InitialGoal t p) (NarradarTRS t v)
mkIGDPProblem (O _ oo) it@(InitialGoal goals g p0) rr dd
    | not $ all isVar (properSubterms =<< concrete goals)
    = error "Initial goals must be of the form f(x,y,z..)"
    | otherwise = oo "dpTRS" dpTRSO $
                  oo "initialGoalProblem" initialGoalProblem goals g $
                  oo "baseProblem" mkDPProblemO p0 rr dd

mapIGP ::
         (t ~ f id, MapId f
         ,v ~ Var
         ,FrameworkId id, DPSymbol id
         ,FrameworkN (InitialGoal t p) t v
         ,FrameworkN p t v
         ,Eq (GoalTerm t), Pretty (GoalTerm t)
         ) => Observer ->
         (NarradarTRS t v -> NarradarTRS t v) ->
         Problem (InitialGoal t p) (NarradarTRS t v) ->
         Problem (InitialGoal t p) (NarradarTRS t v)
mapIGP o f p@(InitialGoalProblem goals g p0)
    = dpTRSO o $ InitialGoalProblem goals g' p'
   where
     p' = mapPO o f p0
     g' = mkDGraphO o p' goals


instance (t ~ f id, MapId f
         ,FrameworkId id, DPSymbol id
         ,FrameworkN (InitialGoal t (MkRewriting st)) t Var
         ,FrameworkN (MkRewriting st) t Var
         ,Eq (GoalTerm t), Pretty (GoalTerm t)
         ,Pretty (MkRewriting st)
         ,Observable st, Typeable st
         ) =>
    MkDPProblem (InitialGoal t (MkRewriting st)) (NarradarTRS t Var)
  where
    mkDPProblemO = mkIGDPProblem
    mapPO = mapIGP
    setP_uncheckedO o pp p = p{baseProblem = setP_uncheckedO o pp (baseProblem p)}

instance (t ~ f id, MapId f
         ,FrameworkId id, DPSymbol id
         ,FrameworkN (MkNarrowing p) t Var
         ,FrameworkN (InitialGoal t (MkNarrowing p)) t Var
         ,Eq (GoalTerm t), Observable(GoalTerm t), Pretty(GoalTerm t)) =>
    MkDPProblem (InitialGoal t (MkNarrowing p)) (NarradarTRS t Var)
  where
  mkDPProblemO = mkIGDPProblem
  mapPO = mapIGP
  setP_uncheckedO o pp p = p{baseProblem = setP_uncheckedO o pp (baseProblem p)}

instance (DPSymbol id, GenSymbol id
         ,FrameworkProblemN (InitialGoal (TermF id) (MkNarrowingGen p)) id
         ,FrameworkProblemN (MkNarrowingGen p) id
         ) =>
    MkDPProblem (InitialGoal (TermF id) (MkNarrowingGen p)) (NTRS id)
  where
  mkDPProblemO = mkIGDPProblem
  mapPO = mapIGP
  setP_uncheckedO o pp p = p{baseProblem = setP_uncheckedO o pp (baseProblem p)}


instance FrameworkExtension (InitialGoal t) where
  getBaseFramework = baseFramework
  getBaseProblem   = baseProblem
  liftProblem   f p = f (baseProblem p) >>= \p0' -> return p{baseProblem = p0'}
  liftFramework f p = p{baseFramework = f $ baseFramework p}
  liftProcessorS = liftProcessorSdefault

initialGoal gg = InitialGoal gg Nothing

initialGoalProblem :: ( t ~ f id, MapId f
                      , FrameworkId id, DPSymbol id
                      , FrameworkN0 typ t Var
                      ) =>
                      Observer
                   -> [CAGoal t]
                   -> Maybe(DGraph t Var)
                   -> Problem typ (NarradarTRS t Var)
                   -> Problem (InitialGoal t typ) (NarradarTRS t Var)

initialGoalProblem o gg Nothing   p = InitialGoalProblem gg (mkDGraphO o p gg) p
initialGoalProblem o gg (Just dg) p = InitialGoalProblem gg dg p

concrete gg = [g | Concrete g <- gg]
abstract gg = [g | Abstract g <- gg]
-- ----------
-- Functions
-- ----------
{-# RULES "Set fromList/toList" forall x. Set.fromList(Set.toList x) = x #-}

initialPairs :: (FrameworkT t, Ord(Term t Var)) => Problem (InitialGoal t base) trs -> [Rule t Var]
initialPairs InitialGoalProblem{..} = dinitialPairs dgraph


-- | returns the vertexes in the DGraph which are in a path from an initial pair to the current P
involvedNodes :: (IsDPProblem base, FrameworkT t, Ord (Term t Var)
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> [Vertex]
involvedNodes p = involvedNodes' (getFramework p) (getP p)

-- | returns the vertexes in the DGraph which are in a path from an initial pair to a given TRS P
involvedNodes' :: (IsDPProblem base, HasId1 t, Foldable t, Ord (Term t Var), HasRules trs
                  ,Rule t Var ~ Family.Rule trs
                  ) => InitialGoal t base -> trs -> [Vertex]
involvedNodes' p@InitialGoal{dgraph_PType=Just dg@DGraph{..},..} pTRS
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

-- | Returns the pairs corresponding to the involved nodes in the DGraph
involvedPairs :: (t ~ f id, MapId f
                 ,FrameworkN (InitialGoal t base) t Var
                 ,IsDPProblem base
                  ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> [Rule t Var]
involvedPairs p@InitialGoalProblem{dgraph=dg@DGraph{..}}
  = map (`lookupPair` dg) (snub(involvedNodes p ++ pairs ++ toList initialPairsG))
 where
   pairs = catMaybes(map (`lookupNode` dg) (rules $ getP p))

involvedPairs p = rules $ getP p

-- NOT POSSIBLE: mkDGraph' expects a DPTRS, whereas dpTRS calls involvedPairs
--involvedPairs p@InitialGoal{goals_PType} trs dps = involvedPairs p{dgraph_PType=Just dg} trs dps
--    where dg = mkDGraph' p trs dps goals_PType

reachableUsableRules :: (t ~ f id, MapId f
                        , FrameworkN base t Var
                        , FrameworkN (InitialGoal t base) t Var
                        ) => Problem (InitialGoal t base) (NarradarTRS t Var)
                          -> NarradarTRS t Var

reachableUsableRules p = getR $ neededRules (getBaseProblem p)
                                            (rhs <$> involvedPairs p)

-- -------------------------------
-- Dependency Graph data structure
-- -------------------------------
type DGraph t v = DGraphF (Term t v)

-- Invariant - the pairs field is always a DPTRS

data DGraphF a = DGraph {pairs    :: NarradarTRSF a            -- ^ A DPTRS storing all the pairs in the problem and the depGraph
                        ,pairsMap :: Map (RuleF a) Vertex      -- ^ Mapping from pairs to vertexes in the sccs graph
                        ,initialPairsG   :: Set Vertex         -- ^ Set of vertexes corresponding to initial pairs
                        ,reachablePairsG :: Set Vertex         -- ^ Set of vertexes corresponding to reachable pairs
                        ,sccs     :: Array Int (SCC Vertex)    -- ^ Array of SCCs in the dep graph
                        ,sccsMap  :: Array Vertex (Maybe Int)  -- ^ Mapping from each vertex to its SCC
                        ,sccGraph :: Graph}                    -- ^ Graph of the reachable SCCs in the dep graph

  deriving (Generic)

deriving instance (HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)) => Eq  (DGraphF a)
deriving instance (HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)) => Ord (DGraphF a)
deriving instance Eq  a => Eq  (SCC a)
deriving instance Ord a => Ord (SCC a)

fullgraph :: NTRSLift a => DGraphF a -> Graph
fullgraph = rulesGraph . pairs

deriving instance Show a => Show (SCC a)
instance (NTRSLift (Term t v), Pretty (Term t v)) => Pretty (DGraph t v) where
  pPrint DGraph{..} = text "DGraphF" <> brackets(vcat [text "pairs =" <+> pPrint (elems $ rulesArray pairs)
                                                      ,text "pairsMap =" <+> pPrint pairsMap
                                                      ,text "initial pairs = " <+> pPrint initialPairsG
                                                      ,text "reachable pairs = " <+> pPrint reachablePairsG
                                                      ,text "graph =" <+> text (show $ rulesGraph pairs)
                                                      ,text "sccs =" <+> text (show sccs)
                                                      ,text "sccsMap =" <+> pPrint (elems sccsMap)
                                                      ,text "sccGraph =" <+> text (show sccGraph)])


mapDGraph :: ( Ord(Term t v), Ord(Term t' v), Foldable t', HasId1 t'
             , Observable v, Observable1 t'
             ) => (Term t v -> Term t' v) -> DGraph t v -> DGraph t' v
mapDGraph f (DGraph p pm ip rp sccs sccsM sccsG)
    = (DGraph (fmap f p) (Map.mapKeys (fmap f) pm) ip rp sccs sccsM sccsG)
{-
mapDGraph' :: ( Ord(Term t v), Ord(Term t' v), Foldable t', HasId t'
              , Observable v, Observable1 t')
           => (Term t v -> Term t' v)
           -> (Rule t v -> Rule t' v)
           -> DGraph t v -> DGraph t' v
mapDGraph' ft fr (DGraph p pm ip rp sccs sccsM sccsG)
    = (DGraph (mapNarradarTRS' ft fr p) (Map.mapKeys fr pm) ip rp sccs sccsM sccsG)
-}

mkDGraph :: ( t ~ f id, MapId f, DPSymbol id
            , FrameworkId id, FrameworkN0 typ t Var
            ) => Problem typ (NarradarTRS t Var) -> [CAGoal t] -> DGraph t Var
mkDGraph = mkDGraphO nilObserver

mkDGraphO :: ( t ~ f id, MapId f, DPSymbol id
            , FrameworkId id, FrameworkN0 typ t Var
            ) => Observer -> Problem typ (NarradarTRS t Var) -> [CAGoal t] -> DGraph t Var
--mkDGraph (getP -> dps) _ | pprTrace ("mkDGraph with pairs: "<> dps) False = undefined
mkDGraphO o p@(lowerNTRS.getP -> DPTRS{dpsA,depGraph=fullgraph}) goals =
 runIcap (rules p) $ do
  let pairsMap = Map.fromList (map swap $ assocs dpsA)

  -- List of indexes for fullgraph
  initialPairsG <- liftM Set.fromList $ runListT $ do
                     (i,s :-> t) <- liftL (assocs dpsA)
                     g           <- liftL goals
                     case g of
                       Concrete g -> do g' <- lift (getFresh g >>= icap p [])
                                        guard(markDP g' `unifies` s)
                                        return i
                       Abstract g -> do guard (rootSymbol g == rootSymbol s)
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
      sccsMap    = array (bounds fullgraph) (zip (indices dpsA) (repeat Nothing) ++
                                         [ (n, Just ix) | (scc,ix,_) <- sccGraphNodes
                                                                   , n <- flattenSCC scc])
      the_dgraph = DGraph {pairs = getP p, ..}


--  pprTrace (text "Computing the dgraph for problem" <+> pPrint (typ, trs, pairs) $$
--            text "The initial pairs are:" <+> pPrint initialPairsG $$
--            text "where the EDG is:" <+> text (show fullgraph)
--            text "The final graph stored is:" <+> text (show graph) $$
--            text "where the mapping used for the nodes is" <+> pPrint (assocs reindexMap) $$
--            text "and the final initial pairs are:" <+> pPrint initialPairsG
--           ) $

  -- The index stored for a pair is within the range of the pairs array
--   assert (all (inRange (bounds pairs)) (Map.elems pairsMap)) $
  -- The scc index stored for a pair is within the range of the sccs array
  assert (all (maybe True (inRange (bounds sccs))) (elems sccsMap)) $
  -- No duplicate edges in the graph
   assert (noDuplicateEdges fullgraph) $
  -- There must be at least one initial pair, right ?
   return the_dgraph

  where
    liftL :: Monad m => [a] -> ListT m a
    liftL = ListT . return

insertDGraphO o p@InitialGoalProblem{..} newdps
    = mkDGraphO o p' goals
  where
    p'     =  insertDPairs (setP (pairs dgraph) p) newdps

expandDGraph ::
      ( t ~ f id, MapId f
      , FrameworkId id, DPSymbol id
      , FrameworkN (InitialGoal t typ) t Var
      , Observable (GoalTerm t)
      ) =>
       Problem (InitialGoal t typ) (NarradarTRS t Var)
    -> Rule t Var
    -> [Rule t Var]
    -> Problem (InitialGoal t typ) (NarradarTRS t Var)
expandDGraph p@InitialGoalProblem{dgraph=dg@DGraph{..},goals} olddp newdps
   = case lookupNode olddp dg of
      Nothing -> p
      Just i  -> p{dgraph=expandDGraph' p i newdps}

expandDGraph' ::
      ( t ~ f id, MapId f
      , FrameworkId id, DPSymbol id
      , FrameworkN (InitialGoal t typ) t Var
      , Observable(GoalTerm t)
      ) =>
       Problem (InitialGoal t typ) (NarradarTRS t Var)
    -> Int
    -> [Rule t Var]
    -> DGraph t Var
expandDGraph' p@InitialGoalProblem{dgraph=dg@DGraph{..},goals} i newdps
  = mkDGraph (expandDPair (setP pairs p) i newdps) goals

data instance Constraints DGraphF a = Ord a => DGraphConstraints
instance Ord a => Suitable DGraphF a where
  constraints = DGraphConstraints

lookupNode p dg = Map.lookup p (pairsMap dg)

lookupPair n dg = safeAt "lookupPair" (rulesArray $ pairs dg) n

sccFor n dg = safeAt "sccFor" (sccsMap dg) n

dreachablePairs DGraph{..} = Set.fromList $ rules pairs

dinitialPairs g = map (safeAt "initialPairs" (rulesArray $ pairs g)) (toList $ initialPairsG g)


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

-- ---------
-- Instances
-- ---------

-- Functor

instance Functor (Problem p) => Functor (Problem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

instance Bifunctor CAGoalF where
  bimap fc fa (Concrete c) = Concrete (fc c)
  bimap fc fa (Abstract a) = Abstract (fa a)

-- Data.Term

-- NFData

instance (NFData p, NFData1 t, NFData(Family.Id t)
         ) => NFData (InitialGoal t p) where
  rnf (InitialGoal g dg b) = rnf g `seq` rnf dg `seq` rnf b

instance (NFData1 t, NFData (Family.Id t), NFData (Problem p trs)) =>
  NFData (Problem (InitialGoal t p) trs)
 where
  rnf (InitialGoalProblem gg g p) = rnf gg `seq` rnf g `seq` rnf p `seq` ()

instance (NFData a, NFData c) => NFData (CAGoalF c a) where
   rnf (Concrete g) = rnf g; rnf (Abstract g) = rnf g

instance (NFData1 t , NFData (Family.Id t), NFData v) => NFData (DGraph t v) where
  rnf (DGraph p pm ip rp sccs sccsm sccg)  = rnf p  `seq`
                                             rnf pm `seq`
                                             rnf ip `seq`
                                             rnf rp `seq`
--                                             rnf sccs `seq`
                                             rnf sccsm `seq`
                                             rnf sccg

-- Output

instance (Pretty (GoalTerm t), Pretty (Term t Var)) => Pretty (CAGoal t) where
  pPrint (Concrete g) = text "concrete" <+> g
  pPrint (Abstract g) = text "abstract" <+> g

instance Pretty p => Pretty (InitialGoal id p) where
    pPrint InitialGoal{..} = text "Initial Goal" <+> pPrint baseFramework


instance (Pretty (Term t Var), Pretty(GoalTerm t), Pretty (Problem base trs)) =>
    Pretty (Problem (InitialGoal t base) trs)
 where
  pPrint InitialGoalProblem{..} =
      pPrint baseProblem $$
      text "GOALS:" <+> pPrint goals


instance HTML p => HTML (InitialGoal id p) where
    toHtml InitialGoal{..} = toHtml "Initial goal " +++ baseFramework

instance HTMLClass (InitialGoal id typ) where htmlClass _ = theclass "G0DP"

instance (Pretty (Term t Var), Pretty (GoalTerm t), PprTPDB (Problem typ trs)) =>
    PprTPDB (Problem (InitialGoal t typ) trs)
 where
    pprTPDB (InitialGoalProblem goals _ p) =
        pprTPDB p $$
        vcat [parens (text "STRATEGY GOAL" <+> g) | g <- goals]


-- ICap

instance (HasRules trs, Unify (Family.TermF trs), GetVars trs
         ,ICap (Problem p trs)) =>
    ICap (Problem (InitialGoal id p) trs)
  where
    icapO = liftIcapO

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
instance (t ~ f id, MapId f
         ,FrameworkN (InitialGoal t p) t Var
         ,trs ~ NarradarTRS t Var
         ,NeededRules (Problem p trs)
         ,IsDPProblem p
         ) =>
          IUsableRules (Problem (InitialGoal (f id) p) (NarradarTRS t Var))
  where
    iUsableRulesVarM p s v = do
      reachable <- neededRulesM p (rhs <$> involvedPairs p)
      iUsableRulesVarM reachable s v

    iUsableRulesM p s tt = do
      reachable <- neededRulesM p =<<
                        getFresh (rhs <$> involvedPairs p)
--      pprTrace( text "The reachable rules are:" <+> pPrint reachable) (return ())
      iUsableRulesM reachable s tt


-- Other Narradar instances

instance ( FrameworkProblemN typ id
         , FrameworkProblemN (InitialGoal (TermF id) typ) id
         , DPSymbol id
         , NeededRules (Problem (InitialGoal (TermF id) typ) (NTRS id))) =>
  InsertDPairs (InitialGoal (TermF id) typ) (NTRS id)
 where
  insertDPairsO o p@InitialGoalProblem{dgraph=DGraph{..},..} newPairs
    = let dgraph' = insertDGraphO o p newPairs
      in insertDPairsDefault o (initialGoalProblem o goals (Just dgraph') baseProblem) newPairs

instance FrameworkProblem (InitialGoal (TermF id) typ) (NTRS id) =>
         ExpandDPair (InitialGoal (TermF id) typ) (NTRS id) where
  expandDPairO = expandDPairOdefault

-------------------------------
-- Hood

instance (Observable p, Observable (GoalTerm t), Observable(Term t Var)) => Observable (InitialGoal t p)
instance (Observable1 (Problem p), Observable1 t)  => Observable1 (Problem (InitialGoal t p))
instance (Observable c, Observable a) => Observable (CAGoalF c a)
instance (Observable a, (Observable (RuleF a))) => Observable (DGraphF a)
