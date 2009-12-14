{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.TRS where

import Control.Applicative
import Control.Arrow (second, (***))
import Control.Exception
import Control.Monad.List
import Data.Suitable
import Data.Array as A
import Data.Array.IArray as A (amap)
import Data.Graph as G (Graph, buildG, edges)
import Data.Foldable as F (Foldable, toList, sum, foldMap)
import Data.Maybe (catMaybes, isJust, isNothing)
import Data.Monoid
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Strict as Strict
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Prelude as P hiding (concatMap)

import Narradar.Types.ArgumentFiltering (ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term hiding ((!))
import Narradar.Types.Var
import Narradar.Constraints.ICap
import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Utils

#ifdef HOOD
import Debug.Observe
#endif

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


data NarradarTRSF a where
    TRS       :: (HasId t, Ord (Term t v)) => Set (Rule t v) -> Signature (TermId t) -> NarradarTRSF (Rule t v)
    PrologTRS :: (HasId t, RemovePrologId (TermId t), Ord (Term t v)) =>
                 Map (WithoutPrologId (TermId t)) (Set (Rule t v)) -> Signature (TermId t) -> NarradarTRSF (Rule t v)
    DPTRS     :: (HasId t, Ord (Term t v)) =>
                 Array Int (Rule t v) -> Graph -> Unifiers t v :!: Unifiers t v -> Signature (TermId t) -> NarradarTRSF (Rule t v)
    ListTRS  -- Used in very few places instead of TRS, when the order of the rules is important
        :: (HasId t, Ord (Term t v)) => [Rule t v] -> Signature (TermId t) -> NarradarTRSF (Rule t v)

type Unifiers t v = Array (Int,Int) (Maybe (Substitution t v))

type NarradarTRS t v = NarradarTRSF (Rule t v)
type NTRS id = NarradarTRS (TermF id) Var

instance Eq (NarradarTRS t v) where
    TRS rr1 _       == TRS rr2 _       = rr1 == rr2
    PrologTRS rr1 _ == PrologTRS rr2 _ = rr1 ==  rr2
    DPTRS rr1 _ _ _ == DPTRS rr2 _ _ _ = rr1 == rr2
    _               == _               = False

instance Ord (NarradarTRS t v) where
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _ _) (DPTRS rr2 _ _ _) = compare rr1 rr2
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT

instance (Ord (Term t v), HasId t, Foldable t) => Monoid (NarradarTRS t v) where
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature $ mconcat $ Map.elems rr)
    mappend (DPTRS r1 _ _ _) (DPTRS r2 _ _ _) =
       let rr = elems r1 `mappend` elems r2 in TRS (Set.fromList rr) (getSignature rr)
    mappend (TRS (Set.null -> True) _) trs = trs
    mappend trs (TRS (Set.null -> True) _) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (Pretty v, Pretty (t(Term t v))) => Pretty (NarradarTRS t v) where
    pPrint trs@TRS{}       = vcat $ map pPrint $ rules trs
    pPrint trs@DPTRS{}     = vcat $ map pPrint $ rules trs
    pPrint trs@PrologTRS{} = vcat $ map pPrint $ rules trs


isNarradarTRS :: NarradarTRS t v -> NarradarTRS t v
isNarradarTRS = id


isNarradarTRS1 :: NarradarTRS (t id) v -> NarradarTRS (t id) v
isNarradarTRS1 = id

listTRS :: (HasId t, Foldable t, Ord (Term t v)) => [Rule t v] -> NarradarTRS t v
listTRS rr = ListTRS rr (getSignature rr)

-- ------------------------------
-- Data.Term framework instances
-- ------------------------------
instance HasRules t v (NarradarTRS t v) where
  rules(TRS       rr _)     = toList rr
  rules(PrologTRS rr _)     = toList $ mconcat (Map.elems rr)
  rules(DPTRS     rr _ _ _) = elems rr
  rules(ListTRS   rr _)     = rr

instance Ord (TermId t) => HasSignature (NarradarTRS t v) where
    type SignatureId (NarradarTRS t v) = TermId t -- SignatureId [Rule (TermF id) v]
    getSignature (TRS         _ sig) = sig
    getSignature (PrologTRS   _ sig) = sig
    getSignature (DPTRS   _ _ _ sig) = sig
    getSignature (ListTRS rr    sig) = sig

instance (Ord (Term t v), Foldable t, HasId t) => IsTRS t v (NarradarTRS t v) where
  tRS  rr = TRS (Set.fromList rr) (getSignature rr)

instance (Ord v, Functor t, Foldable t) => GetVars v (NarradarTRS t v) where getVars = getVars . rules

instance (Traversable t, Ord v, GetFresh t v (Set (Rule t v))) => GetFresh t v (NarradarTRS t v) where
    getFreshM (TRS rr sig) = getFresh (toList rr) >>= \rr' -> return (TRS (Set.fromDistinctAscList rr') sig)
    getFreshM (ListTRS rr sig) = getFresh rr >>= \rr' -> return (ListTRS rr' sig)
    getFreshM (PrologTRS (unzip . Map.toList -> (i, rr)) sig) =
        getFresh rr >>= \rr' -> return (PrologTRS (Map.fromListWith mappend (zip i rr')) sig)
    getFreshM (DPTRS dps_a g uu sig) = getFresh (elems dps_a) >>= \dps' ->
                                       let dps_a' = listArray (bounds dps_a) dps'
                                       in return (DPTRS dps_a' g uu sig)
-- -------------------
-- Narradar instances
-- -------------------

class IUsableRules (TermF id) Var typ (NTRS id) => NUsableRules typ id
instance IUsableRules (TermF id) Var typ (NTRS id) => NUsableRules typ id

class ICap (TermF id) Var (typ, NTRS id) => NCap typ id
instance ICap (TermF id) Var (typ, NTRS id) => NCap typ id


instance (Functor t, Foldable t) => Size (NarradarTRS t v) where size = F.sum . fmap size . rules

instance (Ord (Term t v), ICap t v [Rule t v]) => ICap t v (NarradarTRS t v) where
  icap trs = icap (rules trs)

instance (Ord (Term t v), Foldable t, ApplyAF (Term t v)) => ApplyAF (NarradarTRS t v) where
  type AFId (NarradarTRS t v) = AFId (Term t v)

  apply af (PrologTRS rr _) = prologTRS' ((Map.map . Set.map) (AF.apply af) rr)
  apply af trs@TRS{}        = tRS$ AF.apply af <$$> rules trs
  apply af (DPTRS a g uu _) = tRS (AF.apply af <$$> toList a) -- cannot recreate the graph without knowledge of the problem type
  apply af (ListTRS rr _)   = let rr' = AF.apply af <$$> rr in ListTRS rr' (getSignature rr')

instance (Foldable t, Ord v) =>  ExtraVars v (NarradarTRS t v) where
  extraVars (TRS rr _) = extraVars rr
  extraVars (PrologTRS rr _) = extraVars rr
  extraVars (DPTRS a _ _ _) = extraVars (A.elems a)

instance (ICap t v (typ, NarradarTRS t v), Ord (Term t v), Foldable t, HasId t) => ICap t v (typ, [Rule t v]) where
  icap (typ, p) = icap (typ, mkTRS p)

-- ------------
-- Constructors
-- ------------
mkTRS :: (Ord (Term t v), Foldable t, HasId t) => [Rule t v] -> NarradarTRS t v
mkTRS = tRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS ::  (Ord (Term t v), RemovePrologId (TermId t), Foldable t, HasId t) =>
              [(WithoutPrologId (TermId t), Rule t v)] -> NarradarTRS t v
prologTRS rr = prologTRS' (Map.fromListWith mappend $ map (second Set.singleton) rr)

prologTRS' :: (Ord (Term t v), RemovePrologId (TermId t), Foldable t, HasId t) =>
              Map (WithoutPrologId (TermId t)) (Set(Rule t v)) -> NarradarTRS t v
prologTRS' rr = PrologTRS rr (getSignature rr)

narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)


-- | Assumes that the rules have already been renamed apart
dpTRS :: ( SignatureId trs ~ TermId t
         , Ord (Term t v), HasId t, Unify t, Enum v
         , HasSignature trs, GetFresh t v trs, GetVars v trs, IsTRS t v trs
         , IUsableRules t v typ trs, ICap t v (typ, trs)
         ) =>
         typ -> trs -> trs -> NarradarTRS t v

dpTRS typ trs dps = dpTRS' dps_a unifs
    where
      dps'    = snub (rules dps)
      dps_a   = listArray (0, length dps' - 1) dps'
      unifs   = runIcap dps (computeDPUnifiers typ trs (tRS dps'))

dpTRS' :: ( Foldable t, HasId t, Ord (Term t v)) =>
         Array Int (Rule t v) -> (Unifiers t v :!: Unifiers t v) -> NarradarTRS t v
dpTRS' dps unifiers = DPTRS dps (getEDGfromUnifiers unifiers) unifiers (getSignature $ elems dps)


-- ----------
-- Functions
-- ----------

mapNarradarTRS :: (Ord (Term t v), Ord (Term t' v), Foldable t', HasId t') =>
                  (Term t v -> Term t' v) -> NarradarTRS t v -> NarradarTRS t' v
mapNarradarTRS f (TRS rr sig) = let rr' = Set.map (fmap f) rr in TRS rr' (getSignature rr')
mapNarradarTRS f (PrologTRS rr sig) = error "mapNarradarTRS: PrologTRS - sorry, can't do it"
                                  -- prologTRS (Map.mapKeys f' $ Map.map (fmap f) rr)where f' id = let id' = f (term
mapNarradarTRS f (DPTRS rr g (u1 :!: u2) _) = let rr' = fmap2 f rr
                                              in DPTRS rr' g (fmap3 f u1 :!: fmap3 f u2) (getSignature $ A.elems rr')

mapNarradarTRS' :: (Ord (Term t v), Ord (Term t' v), Foldable t', HasId t') =>
                   (Term t v -> Term t' v) -> (Rule t v -> Rule t' v) -> NarradarTRS t v -> NarradarTRS t' v
mapNarradarTRS' _ fr (TRS rr sig) = let rr' = Set.map fr rr in TRS rr' (getSignature rr')
mapNarradarTRS' _ fr (PrologTRS rr sig) = error "mapNarradarTRS': PrologTRS - sorry, can't do it"
                                  -- prologTRS (Map.mapKeys f' $ Map.map (fmap f) rr)where f' id = let id' = f (term
mapNarradarTRS' ft fr (DPTRS rr g (u1 :!: u2) _) = let rr' = fmap fr rr
                                              in DPTRS rr' g (fmap3 ft u1 :!: fmap3 ft u2) (getSignature $ A.elems rr')

isDPTRS :: NarradarTRSF a -> Bool
isDPTRS DPTRS{} = True; isDPTRS _ = False

restrictTRS :: Foldable t => NarradarTRS t v -> [Int] -> NarradarTRS t v
restrictTRS (TRS rr _) indexes = let rr' = Set.fromList (select indexes (toList rr))
                                   in TRS rr' (getSignature rr')
restrictTRS (PrologTRS rr _) indexes = let rr'  = Map.fromList (select indexes (Map.toList rr))
                                           sig' = getSignature (Map.elems rr')
                                       in PrologTRS rr' (getSignature rr')

restrictTRS (DPTRS dps gr (unif :!: unifInv) _) indexes
  = DPTRS dps' gr' unif' (getSignature $ elems dps')
  where
   newIndexes = Map.fromList (zip indexes [0..])
   nindexes   = length indexes -1
   dps'       = extractIxx dps indexes `asTypeOf` dps
   gr'        = A.amap (catMaybes . map (`Map.lookup` newIndexes)) (extractIxx gr indexes)
   extractIxx arr nodes = A.listArray (0, length nodes - 1) [safeAt "restrictTRS" arr n | n <- nodes]
   unif' = (reindexArray unif :!: reindexArray unifInv)
   reindexArray arr =
           A.array ( (0,0), (nindexes, nindexes) )
                   [ ( (x',y'), sigma) | ((x,y),sigma) <- A.assocs arr
                                       , Just x' <- [Map.lookup x newIndexes]
                                       , Just y' <- [Map.lookup y newIndexes]]

dpUnify, dpUnifyInv :: NarradarTRS t v -> Int -> Int -> Maybe (Substitution t v)
dpUnify    (DPTRS _ _ (unifs :!: _) _) l r = safeAt "dpUnify" unifs (r,l)
dpUnifyInv (DPTRS _ _ (_ :!: unifs) _) l r = safeAt "dpUnifyInv" unifs (r,l)

rulesArray :: NarradarTRS t v -> A.Array Int (Rule t v)
rulesArray (DPTRS dps _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

rulesGraph :: NarradarTRSF a -> Graph
rulesGraph (DPTRS _ g _ _) = g
rulesGraph _ = error "rulesGraph: only DP TRSs carry the dependency graph"


computeDPUnifiers :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , Ord v, Unify t
                     , HasRules t v trs, GetFresh t v trs
                     , IUsableRules t v typ trs
                     , ICap t v (typ, trs)
                     , MonadFresh v m) =>
                     typ -> trs -> trs -> m(unif :!: unif)
--computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers typ trs dps = do
   trs_f <- getFresh trs

   u_rr <- (listArray (0,ldps)) `liftM`
           P.sequence [iUsableRulesM typ trs_f dps [r] | _:->r <- the_dps]

   unif <- computeDirectUnifiers (typ, trs_f) dps
   unifInv <- runListT $ do
                (x, _ :-> r) <- liftL $ zip [0..] the_dps
                (y, l :-> _) <- liftL $ zip [0..] the_dps
                let p_inv = (map swapRule . rules) (u_rr ! x)
                l' <- lift (getFresh l >>= icap p_inv)
                let unifier = unify l' r
                return ((x,y), unifier)

   return (unif :!: array (bounds unif) unifInv)

 where
   the_dps = rules dps
   liftL = ListT . return
   ldps  = length the_dps - 1

computeDirectUnifiers p_f (rules -> the_dps) = do
   rhss'<- P.mapM (\(_:->r) -> getFresh r >>= icap p_f) the_dps
   unif <- runListT $ do
                (x, r')      <- liftL $ zip [0..] rhss'
                (y, l :-> _) <- liftL $ zip [0..] the_dps
                let unifier = unify l r'
--                pprTrace (text "unify" <+> pPrint l <+> pPrint r' <+> equals <+> pPrint unifier) (return ())
                return ((x,y), unifier)
   return $ array ( (0,0), (ldps, ldps) ) unif
 where
   liftL = ListT . return
   ldps  = length the_dps - 1

getEDGfromUnifiers (unif :!: unifInv) = G.buildG (m,n) the_edges where
  the_edges = [ xy | (xy, Just _) <- A.assocs unif
                   , isJust (safeAt "getEDGFromUnifiers" unifInv xy)
                   ]
  ((m,_),(n,_)) = bounds unif


-- -------------------------------
-- Auxiliary Data.Term instances
-- -------------------------------

instance (Ord a, Ord (SignatureId [a]), HasSignature (Set a)) => HasSignature [Set a] where
    type SignatureId [Set a] = SignatureId (Set a)
    getSignature = getSignature . mconcat

instance HasSignature [a] => HasSignature (Map k a) where
    type SignatureId (Map k a) = SignatureId [a]
    getSignature = getSignature . Map.elems

instance (Ord a, GetFresh t v a) => GetFresh t v (Set a) where getFreshM = liftM Set.fromList . getFreshM . Set.toList
instance HasRules t v a => HasRules t v (Set   a) where rules = foldMap rules . toList
instance HasRules t v a => HasRules t v (Map k a) where rules = foldMap rules . Map.elems

instance Pretty (Unifiers t v) where pPrint = pPrint . amap (maybe "N" (const "Y"))