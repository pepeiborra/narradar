{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}

module Narradar.Types.Problem.InitialGoal where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import qualified Control.RMonad as R
import Data.Bifunctor
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Array as A
import Data.Graph as G
import Data.Maybe
import Data.Monoid
import Data.Suitable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Text.XHtml (HTML(..), theclass, (+++))

import Data.Term hiding ((!))
import Data.Term.Rules

import MuTerm.Framework.Problem
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
    { goals_PType     :: [Goal (TermId t)]
    , dgraph_PType    :: Either (forall p. (IsDPProblem p) =>
                                        DPProblem p (NarradarTRS t Var) -> DGraph t Var)
                                (DGraph t Var)
    , baseProblemType :: p}

instance (Eq p, Eq (TermId t)) => Eq (InitialGoal t p) where
    p0 == p1 = (goals_PType p0, baseProblemType p0) == (goals_PType p1, baseProblemType p1)

instance (Ord p, Ord (TermId t)) => Ord (InitialGoal t p) where
    compare p0 p1 = compare (goals_PType p0, baseProblemType p0) (goals_PType p1, baseProblemType p1)

instance (Show p, Show (TermId t)) => Show (InitialGoal t p) where
    show p0 = show (goals_PType p0, baseProblemType p0)

instance Functor (InitialGoal t) where
    fmap f (InitialGoal goals dg p) = InitialGoal goals dg (f p)

instance (IsDPProblem p, HasId t, Foldable t, Ord (Term t Var)) => IsDPProblem (InitialGoal t p) where
  data DPProblem (InitialGoal t p) a = InitialGoalProblem { goals       :: [Goal (TermId t)]
                                                          , dgraph      :: DGraph t Var
                                                          , baseProblem :: DPProblem p a}
  getProblemType (InitialGoalProblem goals g p) = initialGoal goals (getProblemType p)
  mkDPProblem    (InitialGoal goals (Right g)  p) = (InitialGoalProblem goals g .) . mkDPProblem p
  mkDPProblem    (InitialGoal goals (Left mkg) p) = error ("Cannot build an InitialGoal problem with mkDPProblem,"
                                                        ++ " use mkNarradarProblem")
  getP   (InitialGoalProblem _     _ p) = getP p
  getR   (InitialGoalProblem _     _ p) = getR p
  mapR f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapR f p)
  mapP f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapP f p)

initialGoal :: forall typ t.
               ( Ord (Term t Var), HasId t, Foldable t
               , IsDPProblem typ) =>
               [Goal (TermId t)] -> typ -> InitialGoal t typ
initialGoal gg typ = InitialGoal gg (Left mkDG) typ where
  mkDG :: forall typ. IsDPProblem typ => DPProblem typ (NarradarTRS t Var) -> DGraph t Var
  mkDG = mkDGraph gg

initialGoalProblem :: IsDPProblem typ =>
                      [Goal (TermId t)]
                   -> Either (forall typ. IsDPProblem typ =>
                               DPProblem typ trs -> DGraph t Var) (DGraph t Var)
                   -> DPProblem typ trs -> DPProblem (InitialGoal t typ) trs
initialGoalProblem gg (Left mkG) p = InitialGoalProblem gg (mkG p) p
initialGoalProblem gg (Right dg) p = InitialGoalProblem gg dg p

updateInitialGoalProblem p p0 = p{baseProblem = p0}

-- ---------
-- Instances
-- ---------

deriving instance (Eq (Term t Var), Eq (TermId t), Eq (DPProblem p trs)) => Eq (DPProblem (InitialGoal t p) trs)
deriving instance (Ord (t(Term t Var)),  Ord (TermId t), Ord (DPProblem p trs)) => Ord (DPProblem (InitialGoal t p) trs)
deriving instance (Show (TermId t), Show (Term t Var), Show (DPProblem p trs)) => Show (DPProblem (InitialGoal t p) trs)

-- Functor

instance Functor (DPProblem p) => Functor (DPProblem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (DPProblem p) => Foldable (DPProblem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (DPProblem p) => Traversable (DPProblem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

-- Output

instance Pretty p => Pretty (InitialGoal id p) where
    pPrint InitialGoal{..} = text "Initial Goal" <+> pPrint baseProblemType

instance HTML p => HTML (InitialGoal id p) where
    toHtml InitialGoal{..} = toHtml "Initial goal " +++ baseProblemType

instance HTMLClass (InitialGoal id typ) where htmlClass _ = theclass "G0DP"

-- Construction

mkInitialGoalProblem :: (InitialGoal t' p ~ ProblemType (InitialGoal (t id) p) (t id')
                        ,t' ~ TermType (InitialGoal (t id) p) (t id')
                        ,MkNarradarProblem (InitialGoal (t id) p) (t id')
                        ,Foldable (t id), HasId (t id), Ord (Term (t id) Var)
                        ,IsTRS (t id') Var trs
                        ) => InitialGoal (t id) p -> trs -> DPProblem (InitialGoal t' p) (NarradarTRS t' Var)
mkInitialGoalProblem = mkNarradarProblem

instance (Ord id, MapId t, MkNarradarProblem p (t id), TermType p (t id) ~ t(Identifier id)
         ,HasId (t id), Foldable (t id), Ord (Term (t id) Var), TermId (t id) ~ id, TermId (t(Identifier id)) ~ Identifier id
         ,HasId (t(Identifier id)), Foldable (t(Identifier id)), Ord (Term (t(Identifier id)) Var)
         ) =>
    MkNarradarProblem (InitialGoal (t id) p) (t id)
 where
   type ProblemType (InitialGoal (t id) p) (t id) = InitialGoal (t(Identifier id)) (ProblemType p (t id))
   type TermType (InitialGoal (t id) p) (t id) = TermType p (t id)

   mkNarradarProblem (InitialGoal gg (Right g) typ) trs = initialGoalProblem gg' (Right g') p
    where
      p   = mkNarradarProblem typ trs
      gg' = IdDP <$$> gg
      g' = R.fmap (mapTermSymbols IdDP) g

   mkNarradarProblem (InitialGoal gg (Left mkG) typ) trs = initialGoalProblem gg' (Right g) p
    where
      p   = mkNarradarProblem typ trs
      gg' = IdDP <$$> gg
      g = mapTermSymbols IdDP `R.fmap` mkG (mapNarradarTRS (mapTermSymbols symbol) <$> p)


{-
instance (Ord id, MkNarradarProblem p (TermF id), TermType p (TermF id) ~ TermF(Identifier id)) =>
    MkNarradarProblem (InitialGoal (TermF (Identifier id)) p) (TermF (Identifier id))
 where
   type ProblemType (InitialGoal (TermF (Identifier id)) p) (TermF (Identifier id)) = InitialGoal (TermF(Identifier id)) (ProblemType p (TermF (Identifier id)))
   type TermType (InitialGoal (TermF (Identifier id)) p) (TermF (Identifier id)) = TermType p (TermF (Identifier id))

   mkNarradarProblem (InitialGoal gg g typ) trs = initialGoalProblem gg g p
    where
      p   = mkNarradarProblem typ trs
-}
instance (Ord id, MkNarradarProblem p (TermF id), TermType p (TermF id) ~ TermF(Identifier id)) =>
    MkNarradarProblem (InitialGoal (TermF (Identifier id)) p) (TermF id)
 where
   type ProblemType (InitialGoal (TermF (Identifier id)) p) (TermF id) = InitialGoal (TermF(Identifier id)) (ProblemType p (TermF id))
   type TermType (InitialGoal (TermF (Identifier id)) p) (TermF id) = TermType p (TermF id)

   mkNarradarProblem (InitialGoal gg g typ) trs = initialGoalProblem gg g p
    where
      p   = mkNarradarProblem typ trs


-- ICap

instance (HasRules t v trs, Unify t, GetVars v trs, ICap t v (p,trs)) =>
    ICap t v (InitialGoal id p, trs)
  where
    icap (InitialGoal{..},trs) = icap (baseProblemType,trs)

-- Usable Rules

{-
instance IUsableRules t v (DPProblem p trs) =>
    IUsableRules t v (DPProblem (InitialGoal id p) trs)
  where
    iUsableRulesVar InitialGoalProblem{..} = iUsableRulesVar baseProblem
    -- DUMMY IMPLEMENTATION
    iUsableRulesM p@InitialGoalProblem{..} tt = do
      base_p' <- iUsableRulesM baseProblem tt
      return p{baseProblem = base_p'}
-}

instance IUsableRules t v (p, trs) => IUsableRules t v (InitialGoal id p, trs)
  where
    iUsableRulesVar (InitialGoal{..},trs) = iUsableRulesVar (baseProblemType,trs)
    -- DUMMY IMPLEMENTATION
    iUsableRulesM (p@InitialGoal{..},trs) tt = do
      (_,trs') <- iUsableRulesM (baseProblemType,trs) tt
      return (p,trs')

    -- INCOMPLETE IMPLEMENTATION
    {- But note that we would rarely or never use this implementation
       (at least in the case of problems derived from narrowing,)
       In order to be practical,
       the computation of usable rules needs to take into account the argument filtering
       used, and since there is choice, the only practical approach is to encode ALL the
       problem in a propositional formula and solve it using SAT.
       So one would rarely need a separate processor for usable rules.

instance ( IsDPProblem p, Ord id
         , IUsableRules t Var (p, NarradarTRS id Var)
         , IUsableRules t Var (DPProblem p (NarradarTRS id Var))) =>
    IUsableRules t Var (DPProblem (InitialGoal id p) (NarradarTRS id Var))
  where
    iUsableRulesVar InitialGoalProblem{..} = iUsableRulesVar baseProblem

    iUsableRulesM p@InitialGoalProblem{..} tt = do
        let reachable_rhss =
                Set.fromList (rhs <$> rules(getP p))
             `mappend`
                Set.fromList
                [ r
                  | pair <- take 1 $ -- assumption that P is a cycle or SCC
                                     -- (TODO check the assumption)
                            rules (getP p)
                  , let iipp = initialPairs p
                  , _ :-> r <- Set.toList $ foldMap (\p0 -> Set.fromList $ dnodesInPath dgraph p0 pair)
                                                    iipp
                  ]

        (_,reachableRules) <- iUsableRulesM (IRewriting, getR p) (Set.toList reachable_rhss)
        (_,usableRules)    <- iUsableRulesM (baseProblemType (getProblemType p), reachableRules) tt
        return (setR usableRules p)
    -}

-- TODO implementation
-- instance IUsableRules t v (DPProblem (InitialGoal id (Infinitary p)) (NarradarTRS id v))


-- -------------------------------
-- Dependency Graph data structure
-- -------------------------------
type DGraph t v = DGraphF (Term t v)

data DGraphF a = DGraph {pairs    :: Array Int (RuleF a)
                        ,pairsMap :: Map (RuleF a) Int
                        ,initialPairs :: [Int]      -- Indexes for the pairs Array
                        ,graph    :: Graph }
  deriving (Eq, Ord, Show)
--deriving instance (Eq id, Eq v) => Eq (DGraph id v)
--deriving instance (Ord id, Ord v) => Ord (DGraph id v)
--deriving instance (Show id, Show v) => Show (DGraph id v)

instance R.RFunctor DGraphF where
    fmap f dg@(DGraph pa pm ip g) = withResConstraints   $ \DGraphConstraints ->
                                    DGraph (fmap2 f pa) (Map.mapKeys (fmap f) pm) ip g

instance Ord a => Suitable DGraphF a where
    data Constraints DGraphF a = Ord a => DGraphConstraints
    constraints _ = DGraphConstraints


lookupNode p dg = fromMaybe (error "lookupPair: Pair not in graph") $
                  Map.lookup p (pairsMap dg)

lookupPair n dg = pairs dg A.! n

mkDGraph :: (IsDPProblem typ, IsTRS t v trs, HasId t, Ord (Term t v)
            ) => [Goal (TermId t)] -> DPProblem typ trs -> DGraph t v
mkDGraph goals p = DGraph dps_a dps_map initialPairs graph
 where
  dps       = rules $ getP p
  dps_a     = listArray (0,length dps - 1) dps
  dps_map   = Map.fromList (zip dps [0..])
  initialPairs =
     [ i   | (i, pair) <- zip [0..] dps
           , Just id   <- [rootSymbol $ lhs pair]
           , id `Set.member` initialFunctions]

  initialFunctions = foldMap (Set.singleton . goalId) goals
  graph = undefined -- filterSEDG $ getEDG p

dnodesInPath :: (Ord v, Ord (Term t v)) => DGraph t v -> Rule t v -> Rule t v -> [Rule t v]
dnodesInPath dg from to = map (`lookupPair` dg) nodes
    where
       from_node = lookupNode from dg
       to_node   = lookupNode to   dg
       nodes     = nodesInPath (graph dg) from_node to_node

type Node = Int
nodesInPath :: Graph -> Node -> Node -> [Node]
-- TODO Implement as a BF traversal on the graph, modified to accumulate the
--      set of possible predecessor instead of the direct one
nodesInPath g from to = undefined
