{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.TRS where

import Control.Applicative
import Control.Arrow (second, (***))
import Control.Category
import Control.DeepSeq
import Control.Exception
import Control.Monad.List
import Control.Monad.Variant (runVariant)
import Data.Suitable
import Data.Array as A
import Data.Array.IArray as A (amap)
import Data.Graph as G (Graph, buildG, edges)
import Data.Foldable as F (Foldable, toList, sum, foldMap)
import Data.Functor.Two
import Data.Maybe (fromMaybe, catMaybes, isJust, isNothing)
import Data.Monoid
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Strict as Strict
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Data.Typeable
import Prelude as P hiding (concatMap, (.), id)

import qualified Data.Term as Family

import Narradar.Types.ArgumentFiltering (ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Signature
import Narradar.Types.Term hiding ((!), Var)
import Narradar.Types.Var
import Narradar.Constraints.ICap
import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Framework
import Narradar.Framework.Constraints
import Narradar.Framework.Ppr as Ppr hiding ((<>))
import Narradar.Utils hiding (O)

import qualified Data.Id.Family as Family
import qualified Data.Rule.Family as Family
import qualified Data.Term.Family as Family
import qualified Data.Var.Family as Family

import Debug.Hoed.Observe

type FrameworkTRS trs =
  ( IsTRS trs, HasSignature trs, HasRules trs, GetFresh trs
  , GetVars trs, Typeable trs, Observable trs
  , AF.ApplyAF trs
  , FrameworkTerm (Family.TermF trs) (Family.Var trs)
  , Ord trs
  , Monoid trs
  , RuleFor trs ~ Family.Rule trs
  )
type FrameworkProblem0 p trs =
  ( FrameworkTyp p
--  , HasSignature (Problem p id)
  , MkDPProblem p trs
  , IUsableRules (Problem p trs)
  , NeededRules (Problem p trs)
  , Ord (Problem p trs)
  , FrameworkTRS trs
  , NFData p
  , Typeable p
  , Observable p
  , Observable1 (Problem p)
  )

type FrameworkN0 typ t v = FrameworkProblem0 typ (NarradarTRS t v)

isGround :: (Functor t, Foldable t) => Term t v -> Bool
isGround = null . vars

isCollapsing trs = any (isVar.rhs) (rules trs)

-- --------------------
-- TRSs in our setting
-- --------------------

{-
DPTRS contains an additional payload to cache:
1) the graph
2) the unifiers between the pairs computed by the EDG processor.
3) the unifiers computed by the star EDG processor
The unifiers are cached in a matrix (an (rhs,lhs) array) with the following layout
in the case of 2), and the opposite layout in the case of 3)

\ LHS|     |     |
 \   |pair1|pair2|
RHS\ |     |     |
------------------
pair1|_____|_____|
pair2|_____|_____|
.....|     |     |
-}

data NarradarTRS_ a where
    TRS       :: () =>
                 { rulesS :: Set (RuleF a)
                 , sig    :: Signature (Family.Id a)
                 } -> NarradarTRS_ a

    PrologTRS :: (RemovePrologId (Family.Id a)) =>
                 { rulesByClause :: Map (WithoutPrologId (Family.Id a)) (Set (RuleF a))
                 , sig           :: Signature (Family.Id a)
                 } -> NarradarTRS_ a

    DPTRS     :: { typ       :: Comparable
                 , dpsA      :: !(Array Int (RuleF a))
                 , rulesUsed :: Set(RuleF a)
                 , depGraph  :: Graph
                 , unifiers  :: Two (Unifiers a)
                 , sig       :: Signature (Family.Id a)
                 } -> NarradarTRS_ a

      -- | Used in very few places instead of TRS, when the order of the rules is important
    ListTRS :: [RuleF a] -> Signature (Family.Id a) -> NarradarTRS_ a

    deriving Typeable

type instance Family.Id     (NarradarTRSF a) = Family.Id a
type instance Family.Rule   (NarradarTRSF a) = RuleF a
type instance Family.Var    (NarradarTRSF a) = Family.Var a
type instance Family.TermF  (NarradarTRSF a) = Family.TermF a

type instance Family.Id     (NarradarTRS_ a) = Family.Id a
type instance Family.Rule   (NarradarTRS_ a) = RuleF a
type instance Family.Var    (NarradarTRS_ a) = Family.Var a
type instance Family.TermF  (NarradarTRS_ a) = Family.TermF a

type instance Family.Id    (Array i x) = Family.Id x
type instance Family.Rule  (Array i x) = Family.Rule  x
type instance Family.Var   (Array i x) = Family.Var x
type instance Family.TermF (Array i x) = Family.TermF x

class (NFData (Family.Var x), NFData(Family.Id x), NFData x, Observable x, HasId x, Ord(Family.Id x)) => NTRSConstraint x
instance (NFData (Family.Var x), NFData(Family.Id x), NFData x, Observable x, HasId x, Ord(Family.Id x)) => NTRSConstraint x

deriving instance Typeable NTRSConstraint

type NTRSLift x = ( RemovePrologId(Family.Id x), HasSignature x, HasId x, Ord x
                  , NFData(Family.Var x), NFData(Family.Id x), NFData x, Observable x)

type NarradarTRSRestrictedF constraint = NF constraint NarradarTRS_
type NarradarTRSF = NarradarTRSRestrictedF NTRSConstraint

lowerNTRS :: forall c f a. ( Ord a, HasId a, HasSignature(RuleF (a))
                           , c :=># NTRSConstraint
                           , RemovePrologId(Family.Id(RuleF a))) =>
             NarradarTRSRestrictedF c (a) -> NarradarTRS_ (a)
lowerNTRS = lowerNF (fmapNTRS ins) where
  fmapNTRS :: forall x. c(x) => c (x) :- (NTRSConstraint x) -> (x -> a) -> NarradarTRS_ (x) -> NarradarTRS_ (a)
  fmapNTRS (Sub Dict) f (TRS rr sig) = TRS rr' sig' where
      rr'  = Set.map (fmap f) rr
      sig' = getSignature (rules rr') -- TODO surely this is a signature preserving transformation
  fmapNTRS (Sub Dict) f (PrologTRS rr sig) = PrologTRS rr' sig' where
      rr'  = Map.mapKeys fId $ fmap (Set.map (fmap f)) rr
      fId  = fromMaybe (error "lowerNTRS") . join . fmap removePrologId . getId . f . fromId . outId
      sig' = getSignature rr' -- TODO surely this is a signature preserving transformation
  fmapNTRS (Sub Dict) f (ListTRS rr sig) = ListTRS rr' sig' where
      rr' = fmap2 f rr
      sig' = getSignature rr' -- TODO surely this is a signature preserving transformation
  fmapNTRS (Sub Dict) f (DPTRS typ dpsA rulesUsed depGraph unifiers sig) =
    DPTRS typ dpsA' rulesUsed' depGraph unifiers' sig' where
      dpsA' = fmap2 f dpsA
      rulesUsed' = Set.map (fmap f) rulesUsed
      unifiers' = fmap5 f unifiers
      sig' = getSignature dpsA' -- TODO surely this is a signature preserving transformation

type Unifiers a = Array (Int,Int) (Maybe (Two(SubstitutionF a)))
type NarradarTRS t v = NarradarTRSF (Term t v)
type NTRS id = NarradarTRS (TermF id) Var

instance (Ord a) => Eq (NarradarTRS_ a) where
    TRS rr1 _       == TRS rr2 _       = rr1 == rr2
    PrologTRS rr1 _ == PrologTRS rr2 _ = rr1 ==  rr2
    DPTRS _ rr1 _ _ _ _ == DPTRS _ rr2 _ _ _ _ = rr1 == rr2
    ListTRS rr1 _   == ListTRS rr2 _   = Set.fromList rr1 == Set.fromList rr2
    ListTRS rr1 _   == TRS rr2 _       = Set.fromList rr1 == rr2
    TRS rr1 _       == ListTRS rr2 _   = rr1 == Set.fromList rr2
    rr1@DPTRS{dpsA} == rr2@TRS{rulesS} = Set.fromList (elems dpsA) == rulesS
    rr1@TRS{rulesS} == rr2@DPTRS{dpsA} = rulesS == Set.fromList (elems dpsA)
 -- The rest of cases should not occurr at runtime

instance (HasSignature a, HasId a, RemovePrologId(Family.Id a), Ord a) =>
         Eq (NarradarTRSF a) where a == b = lowerNTRS a == lowerNTRS b

instance Ord a => Ord (NarradarTRS_ a) where
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS _ rr1 _ _ _ _) (DPTRS _ rr2 _ _ _ _) = compare rr1 rr2
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT

instance (HasSignature a, HasId a, RemovePrologId(Family.Id a), Ord a) =>
         Ord (NarradarTRSF a) where compare a b = lowerNTRS a `compare` lowerNTRS b

instance (Ord a, HasSignature a, HasId a) => Monoid (NarradarTRS_ a) where
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature $ mconcat $ Map.elems rr)
    mappend (DPTRS _ dp1 _  _ _ _) (DPTRS _ dp2 _ _ _ _) =
       let dps = elems dp1 `mappend` elems dp2
       in tRS dps
    mappend (TRS (Set.null -> True) _) trs = trs
    mappend trs (TRS (Set.null -> True) _) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (NTRSLift a) => Monoid (NarradarTRSF a) where
    mempty = liftNF mempty
    mappend a b = liftNF (mappend (lowerNTRS a) (lowerNTRS b))

instance (Ord a, Pretty a) => Pretty (NarradarTRS_ a) where
    pPrint trs@TRS{}       = vcat $ map pPrint $ rules trs
    pPrint trs@DPTRS{}     = vcat $ map pPrint $ rules trs
    pPrint trs@PrologTRS{} = vcat $ map pPrint $ rules trs
    pPrint (ListTRS  rr _) = vcat $ map pPrint rr
instance (HasId a, HasSignature a, Ord a, Pretty a, RemovePrologId(Family.Id a)) => Pretty(NarradarTRSF a) where pPrint = pPrint . lowerNTRS

instance Foldable NarradarTRS_ where
    foldMap f (TRS rr _) = foldMap2 f rr
    foldMap f (PrologTRS rr _) = foldMap3 f rr
    foldMap f (DPTRS typ dps rr g unif sig) = foldMap2 f rr
    foldMap f (ListTRS rr _) = foldMap2 f rr

instance (NFData a, NFData(Family.Id a), NFData(Family.Var a)) => NFData (NarradarTRS_ a) where
    rnf (TRS rr sig) = rnf rr `seq` rnf sig `seq` ()
    rnf (DPTRS typ dps rr g unif sig) = typ `seq` rnf dps `seq` rnf rr `seq` rnf g `seq` rnf sig `seq` rnf unif `seq` rnf sig
--    rnf (PrologTRS rr sig)    = rnf rr

instance (NFData a, NFData(Family.Id a), NFData(Family.Var a)) => NFData (NarradarTRSF a) where rnf (FMap f x) = rnf f `seq` rnf x

instance (NFData a, NFData b) => NFData (a :!: b) where
    rnf (a :!: b) = rnf a `seq` rnf b `seq` ()

instance Observable1 (NarradarTRS_) where
  observer1 (ListTRS rr sig) = send "ListTRS" (return (`ListTRS` sig) << rr)
  observer1 (TRS rr sig) = send "TRS" (return (`TRS` sig) << rr)
  observer1 (DPTRS typ dpsA ru dg unif sig)
     = send "DPTRS" (return (\typ dpsA dg unif -> DPTRS typ dpsA ru dg unif sig) << typ << dpsA << dg << unif)

instance Observable1 (NarradarTRSF) where
  observer1 (FMap f trs) = FMap f . observer1 trs

isNarradarTRS :: NarradarTRS t v -> NarradarTRS t v
isNarradarTRS = id


isNarradarTRS1 :: NarradarTRS (t id) v -> NarradarTRS (t id) v
isNarradarTRS1 = id

listTRS :: (HasId1 t, Foldable t, NTRSLift (Term t v)
           ) => [Rule t v] -> NarradarTRS t v
listTRS rr = liftNF $ ListTRS rr (getSignature rr)

-- ------------------------------
-- Data.Term framework instances
-- ------------------------------
instance Ord a => HasRules (NarradarTRS_ a) where
  rules(TRS       rr _)       = toList rr
  rules(PrologTRS rr _)       = toList $ mconcat (Map.elems rr)
  rules(DPTRS   _ rr _ _ _ _) = elems rr
  rules(ListTRS   rr _)       = rr
instance (HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)
         ) => HasRules(NarradarTRSF a) where rules = rules . lowerNTRS

instance (Ix i, HasSignature [a]) => HasSignature (Array i a) where
    getSignature = getSignature . toList

instance Ord (Family.Id a) => HasSignature (NarradarTRS_ a) where
    getSignature (TRS           _ sig) = sig
    getSignature (PrologTRS     _ sig) = sig
    getSignature (DPTRS _ _ _ _ _ sig) = sig
    getSignature (ListTRS rr      sig) = sig
instance (Ord a, HasSignature a, NTRSConstraint a, RemovePrologId(Family.Id(NarradarTRSF a))
         ) => HasSignature (NarradarTRSF a) where
    getSignature = getSignature . lowerNTRS

instance (HasId a, HasSignature a, Ord a) => IsTRS (NarradarTRS_ a) where
  tRS  rr = TRS (Set.fromList rr) (getSignature rr)
instance (NTRSLift a
         ) => IsTRS (NarradarTRSF a) where tRS = liftNF . tRS

instance (GetVars a, Ord a) => GetVars (NarradarTRS_ a) where getVars = getVars . rules
instance (GetVars a, Ord a, RemovePrologId(Family.Id a), HasId a, HasSignature a) => GetVars (NarradarTRSF a) where getVars = getVars . lowerNTRS

instance (GetFresh a, Ord(Family.Var a), Ord a
         ) => GetFresh (NarradarTRS_ a) where
    getFreshM (TRS rr sig) = getFresh (toList rr) >>= \rr' -> return (TRS (Set.fromDistinctAscList rr') sig)
    getFreshM (ListTRS rr sig) = getFresh rr >>= \rr' -> return (ListTRS rr' sig)
    getFreshM (PrologTRS (unzip . Map.toList -> (i, rr)) sig) =
        getFresh rr >>= \rr' -> return (PrologTRS (Map.fromListWith mappend (zip i rr')) sig)
    getFreshM (DPTRS typ dps_a rr g uu sig) = getFresh (elems dps_a) >>= \dps' ->
                                       let dps_a' = listArray (bounds dps_a) dps'
                                       in return (DPTRS typ dps_a' rr g uu sig)
instance (GetFresh a, NTRSLift a, Ord(Family.Var a)) => GetFresh(NarradarTRSF a) where
  getFreshM = liftM liftNF . getFreshM . lowerNTRS

instance (Ix i, GetFresh a) => GetFresh(Array i a) where getFreshM = getFreshMdefault
-- -------------------
-- Narradar instances
-- -------------------

type NCap typ id = ICap(Problem typ (NTRS id))
type NUsableRules typ id = IUsableRules(Problem typ id)

instance (Ord a, Size a) => Size (NarradarTRS_ a) where size = F.sum . fmap size . rules

instance (Ord (Term t v), ICap [Rule t v], RemovePrologId (Family.Id t), Ord(Family.Id t), HasId1 t, Foldable t
         ) => ICap (NarradarTRS t v) where
  icapO o trs = icapO o (rules trs)

instance (Ord a, HasId a, HasSignature a, ApplyAF a) => ApplyAF (NarradarTRS_ a) where
  apply af (PrologTRS rr _)    = prologTRS' ((Map.map . Set.map) (AF.apply af) rr)
  apply af trs@TRS{}           = tRS$ AF.apply af <$$> rules trs
  apply af (DPTRS _ a rr g uu _) = tRS (AF.apply af <$$> toList a) -- cannot recreate the graph without knowledge of the problem type
  apply af (ListTRS rr _)      = let rr' = AF.apply af <$$> rr in ListTRS rr' (getSignature rr')

instance (ApplyAF a, NTRSLift a) => ApplyAF(NarradarTRSF a) where
  apply af = liftNF . AF.apply af . lowerNTRS

instance (GetVars a, Ord(Family.Var a)) =>  ExtraVars (NarradarTRS_ a) where
  extraVars (TRS rr _)        = extraVars rr
  extraVars (PrologTRS rr _)  = extraVars rr
  extraVars (DPTRS _ a _ _ _ _) = extraVars (A.elems a)
instance (GetVars a, Ord(Family.Var a), HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)
         ) => ExtraVars (NarradarTRSF a) where extraVars = extraVars . lowerNTRS

-- ------------
-- Constructors
-- ------------
mkTRS :: (Foldable t, HasId1 t, NTRSLift(Term t v)) => [Rule t v] -> NarradarTRS t v
mkTRS = liftNF . tRS

tRS' rr sig  = liftNF $ TRS (Set.fromList rr) sig

prologTRS ::  ( Foldable t, HasId1 t, NTRSLift(Term t v)) =>
              [(WithoutPrologId (Family.Id t), Rule t v)] -> NarradarTRS t v
prologTRS rr = liftNF $ prologTRS' (Map.fromListWith mappend $ map (second Set.singleton) rr)

prologTRS' :: (HasId a, HasSignature a, RemovePrologId(Family.Id a)) =>
              Map (WithoutPrologId (Family.Id a)) (Set(RuleF a)) -> NarradarTRS_ a
prologTRS' rr = PrologTRS rr (getSignature rr)

narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)

dpTRS :: ( rules ~ NarradarTRS t v
         , pairs ~ NarradarTRS t v
         , Observable1 (Problem typ)
         , RemovePrologId (Family.Id t)
         , Eq (Problem typ rules)
         , IUsableRules (Problem typ rules)
         , NeededRules (Problem typ rules)
         , FrameworkTyp typ
         , FrameworkTerm t v
         , MkDPProblem typ rules
         ) =>
          (rules -> Problem typ (NarradarTRS t v) -> Problem typ (NarradarTRS t v))
         -> (pairs -> Problem typ (NarradarTRS t v) -> Problem typ (NarradarTRS t v))
         -> Problem typ (NarradarTRS t v)
         -> Problem typ (NarradarTRS t v)

-- | Takes a Narradar problem and normalizes it, ensuring that the TRS is a consistent DPTRS
--   A consistent DPTRS is that in which the graph and unifiers are consistent with
--   the pairs and rules in the context of the problem type
dpTRS x = dpTRSO nilObserver x

dpTRSO :: ( rules ~ NarradarTRS t v
          , pairs ~ NarradarTRS t v
          , Observable1 (Problem typ)
          , RemovePrologId(Family.Id t)
         , IUsableRules (Problem typ rules)
         , NeededRules (Problem typ rules)
         , Eq (Problem typ rules)
         , FrameworkTyp typ
         , FrameworkTerm t v
         , FrameworkVar v
         , MkDPProblem typ rules
          ) =>
          Observer
       -> (rules -> Problem typ (NarradarTRS t v) -> Problem typ (NarradarTRS t v))
         -> (pairs -> Problem typ (NarradarTRS t v) -> Problem typ (NarradarTRS t v))
         -> Problem typ (NarradarTRS t v)
         -> Problem typ (NarradarTRS t v)

-- | Takes a Narradar problem and normalizes it, ensuring that the TRS is a consistent DPTRS
--   A consistent DPTRS is that in which the graph and unifiers are consistent with
--   the pairs and rules in the context of the problem type
dpTRSO (O o oo) updateRules updatePairs p = updatePairs dps' $ updateRules trs' p
  -- updateRules and updatePairs are versions of Problem.setR and Problem.setP resp.
  -- which do not perform any checks for renormalization. Otherwise we'd have a circular
  -- dependency
  where
        rr = rules $ getR p
        pp = snub $ rules $ getP p
        trs' = tRS rr
        dpsA   = listArray (0, length pp - 1) pp
        temp_p = updatePairs (listTRS pp) $ updateRules trs' p
        -- the use of listTRS here ^ is important to preserve the ordering of pairs
        unifs  = runIcap (rr ++ pp)
                         (oo "computeDirectUnifiers" computeDPUnifiersO temp_p updateRules)
        dps' = oo "dpTRS'" dpTRSO' (Comparable $ getFramework p) dpsA trs' (o "unifs" unifs)


dpTRSO' :: ( Foldable t, HasId1 t
           , Observable v, Observable1 t
           , NTRSLift (Term t v)
           , HasRules rules, Family.Rule rules ~ Rule t v
           ) =>
         Observer -> Comparable -> Array Int (Rule t v) -> rules -> Two (Unifiers(Term t v)) -> NarradarTRS t v
dpTRSO' (O o oo) typ dps rr unifiers =
  liftNF $ DPTRS typ dps (Set.fromList $ rules rr)
                         (o "dg" $ getIEDGfromUnifiers unifiers)
                         unifiers
                         (getSignature $ elems dps)


-- ----------
-- Functions
-- ----------

mapNarradarRules f = liftNF . mapNarradarRules' f . lowerNTRS

mapNarradarRules' :: (Ord (Term t v), HasId1 t, Foldable t, Ord(Family.Id t)) =>
                    (Rule t v -> Rule t v) -> NarradarTRS_ (Term t v) -> NarradarTRS_ (Term t v)
mapNarradarRules' fr (TRS rr sig) = let rr' = Set.map fr rr in TRS rr' (getSignature rr')
mapNarradarRules' fr (PrologTRS rr sig) = error "mapNarradarTRS': PrologTRS - sorry, can't do it"
                                  -- prologTRS (Map.mapKeys f' $ Map.map (fmap f) rr)where f' id = let id' = f (term
mapNarradarRules' fr (DPTRS typ dps rr g uu _)
   = let dps' = fmap fr dps
         rr'  = Set.map fr rr
     in DPTRS typ dps' rr' g uu (getSignature $ A.elems dps')

filterNarradarTRS :: NTRSLift a => (RuleF a -> Bool) -> NarradarTRSF a -> NarradarTRSF a
filterNarradarTRS f = liftNF . tRS . filter f . rules . lowerNTRS

narradarTRStoSet :: (Ord a, HasSignature a, HasId a, RemovePrologId (Family.Id a)) => NarradarTRSF a -> Set (RuleF a)
narradarTRStoSet (lowerNTRS -> TRS{..}) = rulesS
narradarTRStoSet (lowerNTRS -> ListTRS rr _) = Set.fromList rr

isDPTRS :: (HasId a, HasSignature a, Ord a, RemovePrologId (Family.Id a)) => NarradarTRSF a -> Bool
isDPTRS (lowerNTRS -> DPTRS{}) = True; isDPTRS _ = False

restrictTRS :: (Foldable t, HasId1 t
               ,NTRSLift(Term t v)
               ) => NarradarTRS t v -> [Int] -> NarradarTRS t v
restrictTRS = restrictTRSO nilObserver

restrictTRSO :: ( Foldable t, HasId1 t, NTRSLift(Term t v)
                ) => Observer -> NarradarTRS t v -> [Int] -> NarradarTRS t v
restrictTRSO (O o oo) (lowerNTRS -> TRS rr _) indexes = let rr' = Set.fromList (selectSafe "restrictTRS 1" indexes (toList rr))
                                           in mkTRS (toList rr')
restrictTRSO (O o oo) (lowerNTRS -> PrologTRS rr _) indexes =
                                           let rr'  = Map.fromList (selectSafe "restrictTRS 2" indexes (Map.toList rr))
                                               sig' = getSignature (Map.elems rr')
                                           in liftNF $ PrologTRS rr' (getSignature rr')

restrictTRSO (O o oo) (lowerNTRS -> DPTRS typ dps rr gr unif _) indexes
  = liftNF $ DPTRS typ dps' rr gr' unif' (getSignature $ elems dps')
  where
   newIndexes = o "newIndexes" $ Map.fromList (zip indexes [0..])
   nindexes   = length indexes - 1
   dps'       = extractIxx dps indexes `asTypeOf` dps
   gr'        = o "gr'" $ A.amap (catMaybes . map (`Map.lookup` newIndexes)) (extractIxx gr indexes)

   extractIxx :: Array Int a -> [Int] -> Array Int a
   extractIxx arr nodes = A.listArray (0, length nodes - 1) [safeAt "restrictTRS" arr n | n <- nodes]

   unif' = (fmap reindexArray unif)
   reindexArray arr =
           A.array ( (0,0), (nindexes, nindexes) )
                   [ ( (x',y'), sigma) | ((x,y),sigma) <- A.assocs arr
                                       , Just x' <- [Map.lookup x newIndexes]
                                       , Just y' <- [Map.lookup y newIndexes]]

dpUnify, dpUnifyInv :: (HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)) =>
                        NarradarTRSF a -> Int -> Int -> Maybe (Two(SubstitutionF a))
dpUnify    (lowerNTRS -> DPTRS _ _ _ _ (Two unifs _) _) l r = safeAt "dpUnify"    unifs (r,l)
dpUnifyInv (lowerNTRS -> DPTRS _ _ _ _ (Two _ unifs) _) l r = safeAt "dpUnifyInv" unifs (r,l)

rulesArray :: (HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)) =>
              NarradarTRSF a -> A.Array Int (RuleF a)
rulesArray (lowerNTRS -> DPTRS _ dps _ _ _ _) = dps
rulesArray (lowerNTRS -> TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

rulesGraph :: (HasId a, HasSignature a, Ord a, RemovePrologId(Family.Id a)) => NarradarTRSF a -> Graph
rulesGraph (lowerNTRS -> DPTRS _ _ _ g _ _) = g
rulesGraph _ = error "rulesGraph: only DP TRSs carry the dependency graph"

computeDPUnifiers x = computeDPUnifiersO nilObserver x

computeDPUnifiersO :: forall unif typ trs t v term m rules.
                     ( unif ~ Unifiers (Term t v)
                     , term ~ Term t v
                     , t ~ Family.TermF trs
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , Rule t v ~ Family.Rule trs
                     , rules ~ trs
                     , IsTRS trs, HasRules trs, GetFresh trs
                     , FrameworkTyp typ
                     , FrameworkTerm (Family.TermF trs) (Family.Var trs)
                     , MkDPProblem typ trs
                     , Eq (Problem typ trs)
                     , ICap (Problem typ trs)
                     , IUsableRules (Problem typ trs)
                     , NeededRules  (Problem typ trs)
                     , Observable1  (Problem typ)
                     , Observable1 m
                     , Observable trs
                     , MonadVariant m) =>
                     Observer
                     -> Problem typ trs
                     -> (rules -> Problem typ trs -> Problem typ trs)
                     -> m(Two unif)
computeDPUnifiersO (O o oo) p updateRules = do
   unif    <- oo "direct unifiers"  computeDirectUnifiersO  p
   unifInv <- oo "inverse unifiers" computeInverseUnifiersO p updateRules
   return (Two unif unifInv)

computeDirectUnifiers x = computeDirectUnifiersO nilObserver x

computeDirectUnifiersO :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers (Term t v)
                     , term ~ Term t v
                     , t ~ Family.TermF trs
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , Rule t v ~ Family.Rule trs
                     , Ord v, Unify t
                     , HasRules trs, GetFresh trs
                     , IsDPProblem typ
                     , ICap (Problem typ trs)
                     , Pretty (Term t v), Pretty v
                     , Observable (Term t v), Observable trs, Observable typ
                     , MonadVariant m
                     , Observable v
                     , Observable1 m
                     , Observable1 t
                     ) =>
                     Observer -> Problem typ trs -> m unif
computeDirectUnifiersO (O o oo) p_f =
  let the_dps = rules $ getP p_f
      ldps  = length the_dps - 1
      doOne (O o _) (x, s:->t) (y, u:->v) = do
         (_:->t'', u1) <- runMEnv $ o "getFreshM"  getFreshM (s:->t)
         (u':->v', u2) <- runMEnv $ o "getFreshM2" getFreshM (u:->v)
         t'            <- icap p_f [s,u] t''
         let sigma = o "unify" unify u' t'
                -- pprTrace (vcat [text "unify" <+> (u <+> text "with" <+> t')
                --                ,parens (text "icap" <+> (rules(snd p_f) $$ t))
                --                ,equals <+> unifier]) (return ())
         return ((x,y), fmap (\sigma -> Two (o "u1" u1 <> o "sigma" sigma)
                                            (o "u2" u2 <> sigma)
                             )
                             sigma)
   in do
     unif <- runListT $ do
                rule1 <- liftL $ zip [0..] the_dps
                rule2 <- liftL $ zip [0..] the_dps
                oo "doOne" doOne rule1 rule2
     return $ array ( (0,0), (ldps, ldps) ) unif


computeInverseUnifiersO :: forall unif typ trs t v term m rules.
                     ( unif ~ Unifiers (Term t v)
                     , term ~ Term t v
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , t ~ Family.TermF trs
                     , Rule t v ~ Family.Rule trs
                     , FrameworkTyp typ
                     , FrameworkTerm (Family.TermF trs) (Family.Var trs)
                     , MonadVariant m
                     , Observable1 m
                     , rules ~ trs, HasRules trs, IsTRS trs
                     , IUsableRules (Problem typ trs)
                     ) =>
                     Observer
                     -> Problem typ trs
                     -> (rules -> Problem typ trs -> Problem typ trs)
                     -> m unif
--computeInverseUnifiers _ _ | trace "computeInverseUnifiers" False = undefined
computeInverseUnifiersO (O o oo) p updateR = do
   let dps   = rules $ getP p
   let ldps  = length dps - 1
   unif <- runListT $ do
                (x, s :-> t) <- liftL $ zip [0..] dps
                (y, u :-> v) <- liftL $ zip [0..] dps
                u_rr <- {-o "usableRules"-} iUsableRulesM p [s,u] [t]
                let p_inv = updateR (tRS $ map swapRule (rules $ getR u_rr)) p
                (s':->t', u1) <- lift (runMEnv $ getFreshM (s:->t))
                (u':->_,  u2) <- lift (runMEnv $ getFreshM (u:->v))
                u'' <- lift ({-o"icap"-} icap p_inv [] u')
                let sigma = {-o "unify"-} Narradar.Constraints.Unify.unify u'' t'
--                pprTrace (text "unify" <+> l' <+> parens (text "icap" <+> p_inv <+> l)
--                          <+> text "with" <+> r <+> equals <+> unifier) (return ())
                return ((x,y), fmap (\sigma -> Two (u1<>sigma) (u2<>sigma)) sigma)
   return $ array ((0,0), (ldps,ldps)) unif


getIEDGfromUnifiers (Two unif unifInv) = G.buildG (m,n) the_edges where
  the_edges = [ xy | (xy, Just _) <- A.assocs unif
                   , isJust (safeAt "getIEDGFromUnifiers" unifInv xy)
                   ]
  ((m,_),(n,_)) = bounds unif

getEDGfromUnifiers = getEDGfromUnifiersO nilObserver
getEDGfromUnifiersO (O o oo) (Two unif _) = G.buildG (m,n) the_edges where
  the_edges = [ xy | (xy, Just _) <- A.assocs unif
                   ]
  ((m,_),(n,_)) = bounds unif


instance Pretty (Unifiers a) where pPrint = pPrint . amap (maybe "N" (const "Y"))

