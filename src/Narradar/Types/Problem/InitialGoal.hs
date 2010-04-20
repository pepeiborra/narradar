{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}

module Narradar.Types.Problem.InitialGoal where

import Control.Applicative
import Control.DeepSeq
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
import Narradar.Types.Problem.Narrowing hiding (baseProblem)
import Narradar.Types.Problem.NarrowingGen hiding (baseProblem, baseFramework)
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
    , baseFramework :: p}

instance (Eq p, Eq (Term t Var)) => Eq (InitialGoal t p) where
    p0 == p1 = (goals_PType p0, baseProblemType p0) == (goals_PType p1, baseProblemType p1)

instance (Ord p, Ord (Term t Var)) => Ord (InitialGoal t p) where
    compare p0 p1 = compare (goals_PType p0, baseProblemType p0) (goals_PType p1, baseProblemType p1)

instance (Show p, Show (Term t Var)) => Show (InitialGoal t p) where
    show p0 = show (goals_PType p0, baseProblemType p0)

instance Functor (InitialGoal t) where
    fmap f (InitialGoal goals dg p) = InitialGoal goals dg (f p)

mapInitialGoal f (InitialGoal goals dg p) = InitialGoal goals' dg' p
      where
        goals' = fmap (foldTerm return f') goals
        dg'    = mapDGraph (foldTerm return f') <$> dg
        f'     = Impure . f

instance (IsProblem p, HasId t, Foldable t) => IsProblem (InitialGoal t p) where
  data Problem (InitialGoal t p) a = InitialGoalProblem { goals       :: [Term t Var]
                                                        , dgraph      :: DGraph t Var
                                                        , baseProblem :: Problem p a}
  getProblemType (InitialGoalProblem goals g p) = InitialGoal goals (Just g) (getProblemType p)
  getR   (InitialGoalProblem _     _ p) = getR p

instance ( t ~ f id, MapId f, DPSymbol id
         , MkDPProblem p (NarradarTRS t Var)
         , HasId t, Foldable t, Unify t
         , Ord (Term t Var), Pretty (t(Term t Var))
         , Traversable (Problem p), Pretty p
         , ICap t Var (p, NarradarTRS t Var)
         , IUsableRules t Var p (NarradarTRS t Var)
         ) =>
     MkProblem (InitialGoal t p) (NarradarTRS t Var)
 where
  mkProblem (InitialGoal gg gr p) rr = initialGoalProblem gg gr (mkProblem p rr)
  mapR f (InitialGoalProblem goals _ p) = initialGoalProblem goals Nothing (mapR f p)

instance (IsDPProblem p, HasId t, Foldable t) => IsDPProblem (InitialGoal t p) where
  getP   (InitialGoalProblem _     _ p) = getP p

instance (t ~ f id, MapId f, DPSymbol id
         ,HasId t, Unify t, Foldable t, Pretty p
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

initialGoalProblem :: ( t ~ f id, MapId f, DPSymbol id
                      , HasId t, Unify t, Ord (Term t Var), Pretty (t(Term t Var))
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
involvedNodes p = involvedNodes' (getFramework p) (getP p)

-- | returns the vertexes in the DGraph which are in a path from an initial pair to a given TRS P
involvedNodes' :: (IsDPProblem base, HasId t, Foldable t, Ord (Term t Var)
                  ,HasRules t Var trs
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
involvedPairs :: (t ~ f id, HasId t, MapId f, Foldable t, Unify t
                 ,IsDPProblem base, Traversable (Problem base)
                 ,Ord (Term t Var)
                 ,ICap t Var (base, NarradarTRS t Var)
                 ,IUsableRules t Var base (NarradarTRS t Var)
                 ,Pretty base, Pretty (Term t Var)
                 ,DPSymbol id
                  ) => InitialGoal t base -> NarradarTRS t Var -> NarradarTRS t Var -> [Rule t Var]
involvedPairs p@InitialGoal{dgraph_PType=Just dg@DGraph{..}} trs dps
  = map (`lookupPair` dg) (snub(involvedNodes' p dps ++ pairs ++ toList initialPairsG))
 where
   pairs = catMaybes(map (`lookupNode` dg) (rules dps))

involvedPairs p trs dps = rules dps

-- NOT POSSIBLE: mkDGraph' expects a DPTRS, whereas dpTRS calls involvedPairs
--involvedPairs p@InitialGoal{goals_PType} trs dps = involvedPairs p{dgraph_PType=Just dg} trs dps
--    where dg = mkDGraph' p trs dps goals_PType

reachableUsableRules :: (t ~ f id, Ord(Term t Var), HasId t, Foldable t, Unify t, MapId f
                        ,MkDPProblem base (NarradarTRS t Var), Traversable (Problem base)
                        ,ICap t Var (base, NarradarTRS t Var)
                        ,IUsableRules t Var base (NarradarTRS t Var)
                        ,NeededRules t Var base (NarradarTRS t Var)
                        ,Pretty base, Pretty (Term t Var)
                        ,DPSymbol id
                        ) => Problem (InitialGoal t base) (NarradarTRS t Var) -> NarradarTRS t Var

reachableUsableRules p = getR $ neededRules (getBaseProblem p) (rhs <$> forDPProblem involvedPairs p)

-- ---------
-- Instances
-- ---------

-- Functor

instance Functor (Problem p) => Functor (Problem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (Problem p) => Foldable (Problem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (Problem p) => Traversable (Problem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

-- Data.Term

-- NFData

instance (NFData (t(Term t Var)), NFData (TermId t), NFData (Problem p trs)) => NFData (Problem (InitialGoal t p) trs) where
  rnf (InitialGoalProblem gg g p) = rnf gg `seq` rnf g `seq` rnf p `seq` ()

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
    toHtml InitialGoal{..} = toHtml "Initial goal " +++ baseFramework

instance HTMLClass (InitialGoal id typ) where htmlClass _ = theclass "G0DP"


instance (Pretty (Term t Var), PprTPDB (Problem typ trs)) =>
    PprTPDB (Problem (InitialGoal t typ) trs)
 where
    pprTPDB (InitialGoalProblem goals _ p) =
        pprTPDB p $$
        vcat [parens (text "STRATEGY GOAL" <+> g) | g <- goals]


-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (InitialGoal id p, trs)
  where
    icap (InitialGoal{..},trs) = icap (baseFramework,trs)

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
instance (t ~ f id, MapId f, HasId t, Foldable t, Unify t
         ,Ord (t(Term t Var)), Pretty (t(Term t Var))
         ,IsDPProblem p, Traversable (Problem p), Pretty p
         ,DPSymbol id
         ,trs ~ NarradarTRS t Var
         ,ICap t Var (p, trs)
         ,IUsableRules t Var p trs
         ) =>
          IUsableRules (f id) Var (InitialGoal (f id) p) trs
  where
    iUsableRulesVarM it@(InitialGoal _ _ p) trs dps v = do
      reachableRules <- iUsableRulesM irewriting trs dps (rhs <$> involvedPairs it trs dps)
      iUsableRulesVarM p reachableRules dps v

    iUsableRulesM it@(InitialGoal _ _ p) trs dps tt = do
      reachableRules <- iUsableRulesM irewriting trs dps =<< getFresh (rhs <$> involvedPairs it trs dps)
--      pprTrace( text "The reachable rules are:" <+> pPrint reachableRules) (return ())
      iUsableRulesM p reachableRules dps tt


-- Other Narradar instances

instance (trs ~ NTRS id
         ,MkDPProblem typ trs, Pretty typ, Traversable (Problem typ)
         ,Pretty id, Ord id, DPSymbol id
         ,NUsableRules typ id
         ,NCap typ id
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
type DGraph t v = DGraphF (Term t v)

-- Invariant - the pairs field is always a DPTRS

data DGraphF a = DGraph {pairs    :: NarradarTRSF (RuleF a)    -- ^ A DPTRS storing all the pairs in the problem and the depGraph
                        ,pairsMap :: Map (RuleF a) Vertex      -- ^ Mapping from pairs to vertexes in the sccs graph
                        ,initialPairsG   :: Set Vertex         -- ^ Set of vertexes corresponding to initial pairs
                        ,reachablePairsG :: Set Vertex         -- ^ Set of vertexes corresponding to reachable pairs
                        ,sccs     :: Array Int (SCC Vertex)    -- ^ Array of SCCs in the dep graph
                        ,sccsMap  :: Array Vertex (Maybe Int)  -- ^ Mapping from each vertex to its SCC
                        ,sccGraph :: Graph}                    -- ^ Graph of the reachable SCCs in the dep graph

fullgraph :: DGraph t v -> Graph
fullgraph = rulesGraph . pairs

deriving instance Show a => Show (SCC a)
instance Pretty (Term t v) => Pretty (DGraph t v) where
  pPrint DGraph{..} = text "DGraphF" <> brackets(vcat [text "pairs =" <+> pPrint (elems $ rulesArray pairs)
                                                      ,text "pairsMap =" <+> pPrint pairsMap
                                                      ,text "initial pairs = " <+> pPrint initialPairsG
                                                      ,text "reachable pairs = " <+> pPrint reachablePairsG
                                                      ,text "graph =" <+> text (show $ rulesGraph pairs)
                                                      ,text "sccs =" <+> text (show sccs)
                                                      ,text "sccsMap =" <+> pPrint (elems sccsMap)
                                                      ,text "sccGraph =" <+> text (show sccGraph)])

instance (NFData (t(Term t v)), NFData (TermId t), NFData v) => NFData (DGraph t v) where
  rnf (DGraph p pm ip rp sccs sccsm sccg)  = rnf p  `seq`
                                             rnf pm `seq`
                                             rnf ip `seq`
                                             rnf rp `seq`
--                                             rnf sccs `seq`
                                             rnf sccsm `seq`
                                             rnf sccg

mapDGraph f (DGraph p pm ip rp sccs sccsM sccsG)
    = (DGraph (mapNarradarTRS f p) (Map.mapKeys (fmap f) pm) ip rp sccs sccsM sccsG)

mkDGraph :: ( t ~ f id, MapId f, DPSymbol id
            , v ~ Var
            , MkDPProblem typ (NarradarTRS t v)
            , Traversable (Problem typ), Pretty typ
            , HasId t, Unify t
            , Pretty ((Term t v))
            , Ord    (Term t v)
            , ICap t v (typ, NarradarTRS t v)
            , IUsableRules t v typ (NarradarTRS t v)
            ) => Problem typ (NarradarTRS t v) -> [Term t v] -> DGraph t v

mkDGraph p@(getP -> DPTRS _ _ gr _ _) gg = mkDGraph' (getProblemType p) (getR p) (getP p) gg

mkDGraph' :: ( t ~ f id, DPSymbol id, MapId f
             , v ~ Var
             , IsDPProblem typ, Traversable (Problem typ), Pretty typ
             , HasId t, Unify t, Pretty (Term t v)
             , ICap t v (typ, NarradarTRS t v)
             ) => typ -> NarradarTRS t v -> NarradarTRS t v -> [Term t v] -> DGraph t v
mkDGraph' typ trs pairs@(DPTRS dps_a _ fullgraph _ _) goals = runIcap (rules trs ++ rules pairs) $ do
  let pairsMap = Map.fromList (map swap $ assocs dps_a)
      p   = (typ,trs)

  -- List of indexes for fullgraph
  initialPairsG <- liftM Set.fromList $ runListT $ do
                     (i,s :-> t) <- liftL (assocs dps_a)
                     g           <- liftL goals
                     g'          <- lift (getFresh g >>= icap p)
                     guard(markDP g' `unifies` s)
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
      sccsMap    = array (bounds fullgraph) (zip (indices dps_a) (repeat Nothing) ++
                                         [ (n, Just ix) | (scc,ix,_) <- sccGraphNodes
                                                                   , n <- flattenSCC scc])
      the_dgraph = DGraph {..}


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
   assert (not $ Set.null initialPairsG)
   return the_dgraph

  where liftL = ListT . return

insertDGraph p@InitialGoalProblem{..} newdps
    = mkDGraph' (getFramework p') (getR p') dps' goals
  where
    p'     =  insertDPairs (setP (pairs dgraph) p) newdps
    dps'   = getP p'
{-
expandDGraph ::
      ( Traversable (Problem typ), Pretty typ
      , MkDPProblem typ (NarradarTRS t Var)
      , ICap t Var (typ, NarradarTRS t Var)
      , IUsableRules t Var typ [Rule t Var] -- (NarradarTRS t Var)
      , IUsableRules t Var typ (NarradarTRS t Var)
      ) =>
      Problem (InitialGoal t typ) (NarradarTRS t Var) -> Rule t Var -> [Rule t Var] -> DGraph t Var
-}
expandDGraph p@InitialGoalProblem{dgraph=dg@DGraph{..},goals} olddp newdps
   = case lookupNode olddp dg of
      Nothing -> dg
      Just i -> expandDGraph' p i newdps

expandDGraph' p@InitialGoalProblem{dgraph=dg@DGraph{..},goals} i newdps
   = let p' = expandDPair (setP pairs p) i newdps
     in mkDGraph p' goals

instance Ord a => Suitable DGraphF a where
  data Constraints DGraphF a = Ord a => DGraphConstraints
  constraints _ = DGraphConstraints

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
