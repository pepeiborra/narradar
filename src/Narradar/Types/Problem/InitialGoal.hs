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

data InitialGoal id p = InitialGoal
    { goals_PType     :: [Goal id]
    , dgraph_PType    :: Either (forall p. IsDPProblem p => NarradarProblem p id -> DGraph id Var)
                                (DGraph id Var)
    , baseProblemType :: p}

instance (Eq p, Eq id) => Eq (InitialGoal id p) where
    p0 == p1 = (goals_PType p0, baseProblemType p0) == (goals_PType p1, baseProblemType p1)

instance (Ord p, Ord id) => Ord (InitialGoal id p) where
    compare p0 p1 = compare (goals_PType p0, baseProblemType p0) (goals_PType p1, baseProblemType p1)

instance (Show p, Show id) => Show (InitialGoal id p) where
    show p0 = show (goals_PType p0, baseProblemType p0)

instance Functor (InitialGoal id) where
    fmap f (InitialGoal goals dg p) = InitialGoal goals dg (f p)

instance (Ord id, IsDPProblem p) => IsDPProblem (InitialGoal id p) where
  data DPProblem (InitialGoal id p) a = InitialGoalProblem { goals       :: [Goal id]
                                                               , dgraph      :: DGraph id Var
                                                               , baseProblem :: DPProblem p a}
  getProblemType (InitialGoalProblem goals g p) = initialGoal goals (getProblemType p)
  mkDPProblem    (InitialGoal goals (Right g)  p) = (InitialGoalProblem goals g .) . mkDPProblem p
  mkDPProblem    (InitialGoal goals (Left mkg) p) = error ("Cannot build an InitialGoal problem with mkDPProblem,"
                                                        ++ " use mkNarradarProblem")
  getP   (InitialGoalProblem _     _ p) = getP p
  getR   (InitialGoalProblem _     _ p) = getR p
  mapR f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapR f p)
  mapP f (InitialGoalProblem goals g p) = InitialGoalProblem goals g (mapP f p)

initialGoal :: forall id typ.
               ( --trs ~ NarradarTRS id Var, Ord id
--                 HasRules (TermF id) Var trs
                Ord id
               , IsDPProblem typ) =>
               [Goal id] -> typ -> InitialGoal id typ
initialGoal gg typ = InitialGoal gg (Left mkDG) typ where
  mkDG :: forall typ. IsDPProblem typ => NarradarProblem typ id -> DGraph id Var
  mkDG = mkDGraph gg

initialGoalProblem :: IsDPProblem typ =>
                      [Goal id]
                   -> Either (forall typ. IsDPProblem typ => DPProblem typ trs -> DGraph id Var) (DGraph id Var)
                   -> DPProblem typ trs -> DPProblem (InitialGoal id typ) trs
initialGoalProblem gg (Left mkG) p = InitialGoalProblem gg (mkG p) p
initialGoalProblem gg (Right dg) p = InitialGoalProblem gg dg p


deriving instance (Eq id, Eq (DPProblem p trs)) => Eq (DPProblem (InitialGoal id p) trs)
deriving instance (Ord id, Ord (DPProblem p trs)) => Ord (DPProblem (InitialGoal id p) trs)
deriving instance (Ppr (Identifier id), Show id, Show (DPProblem p trs)) => Show (DPProblem (InitialGoal id p) trs)

instance Functor (DPProblem p) => Functor (DPProblem (InitialGoal id p)) where fmap f (InitialGoalProblem gg g p) = InitialGoalProblem gg g (fmap f p)
instance Foldable (DPProblem p) => Foldable (DPProblem (InitialGoal id p)) where foldMap f (InitialGoalProblem gg g p) = foldMap f p
instance Traversable (DPProblem p) => Traversable (DPProblem (InitialGoal id p)) where traverse f (InitialGoalProblem gg g p) = InitialGoalProblem gg g <$> traverse f p

-- Output

instance Ppr p => Ppr (InitialGoal id p) where
    ppr InitialGoal{..} = text "Initial Goal" <+> ppr baseProblemType

instance HTML p => HTML (InitialGoal id p) where
    toHtml InitialGoal{..} = toHtml "Initial goal " +++ baseProblemType

instance HTMLClass (InitialGoal id typ) where htmlClass _ = theclass "G0DP"

instance (Ord id, Ppr id, MkNarradarProblem p id) =>
    MkNarradarProblem (InitialGoal id p) id
 where
   type Typ' (InitialGoal id p) id = InitialGoal (Identifier id) (Typ' p id)

   mkNarradarProblem (InitialGoal gg (Right g) typ) trs = initialGoalProblem gg' (Right g') p
    where
      p   = mkNarradarProblem typ trs
      gg' = IdDP <$$> gg
      g' = R.fmap (mapTermSymbols IdDP) g

   mkNarradarProblem (InitialGoal gg (Left mkG) typ) trs = initialGoalProblem gg' (Left mkG') p
    where
      p   = mkNarradarProblem typ trs
      gg' = IdDP <$$> gg
      mkG' :: forall p. IsDPProblem p => NarradarProblem p (Identifier id) -> DGraph (Identifier id) Var
      mkG' p = R.fmap (mapTermSymbols IdDP) (mkG (mapNarradarTRS (mapTermSymbols symbol) `fmap` p))


instance (Ord id, Ppr (Identifier id), MkNarradarProblem p id) =>
    MkNarradarProblem (InitialGoal (Identifier id) p) id
 where
   type Typ' (InitialGoal (Identifier id) p) id
          = InitialGoal (Identifier id) (Typ' p id)
   mkNarradarProblem (InitialGoal gg g typ) trs = initialGoalProblem gg g p where
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
type DGraph id v = DGraphF (TermN id v)

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

dnodesInPath :: (Ord v, Ord id) => DGraph id v -> RuleN id v -> RuleN id v -> [RuleN id v]
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
