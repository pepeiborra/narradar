{-# LANGUAGE ScopedTypeVariables #-}
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
import Data.Graph (Graph, buildG, edges)
import Data.Foldable as F (Foldable, toList, sum, foldMap)
import Data.Maybe (catMaybes, isJust)
import Data.Monoid
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Text.PrettyPrint
import Prelude as P hiding (concatMap)

import Narradar.Types.ArgumentFiltering (ApplyAF)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term hiding ((!))
import Narradar.Types.Var
import Narradar.Constraints.ICap
import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Framework
import Narradar.Framework.Ppr
import Narradar.Utils

#ifdef HOOD
import Debug.Observe
#endif

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
    TRS       :: Set (Rule t v) -> Signature (TermId t) -> NarradarTRSF (Term t v)
    PrologTRS :: (HasId t, RemovePrologId (TermId t)) =>
                 Map (WithoutPrologId (TermId t)) (Set (Rule t v)) -> Signature (TermId t) -> NarradarTRSF (Term t v)
    DPTRS     :: HasId t =>
                 Array Int (Rule t v) -> !Graph -> Unifiers t v :!: Unifiers t v -> Signature (TermId t) -> NarradarTRSF (Term t v)

type Unifiers t v = Array (Int,Int) (Maybe (Substitution t v))

type NarradarTRS id v = NarradarTRSF (TermN id v)

instance (Ord id, Ord v) => Eq (NarradarTRS id v) where trs1 == trs2 = rules trs1 == rules trs2

instance (Ord id, Ord v) => Ord (NarradarTRS id v) where
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _ _) (DPTRS rr2 _ _ _) = compare rr1 rr2
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT

instance (Ord v, Ord id) => Monoid (NarradarTRS id v) where
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature rr)
    mappend (DPTRS r1 _ _ _) (DPTRS r2 _ _ _) =
       let rr = elems r1 `mappend` elems r2 in TRS (Set.fromList rr) (getSignature rr)
    mappend (TRS (Set.null -> True) _) trs = trs
    mappend trs (TRS (Set.null -> True) _) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (Ord v, Ppr v, Ord id, Ppr id) => Ppr (NarradarTRS id v) where
    ppr trs@TRS{}       = vcat $ map ppr $ rules trs
    ppr trs@DPTRS{}     = vcat $ map ppr $ rules trs
    ppr trs@PrologTRS{} = vcat $ map ppr $ rules trs


-- ------------------------------
-- Data.Term framework instances
-- ------------------------------
instance (Ord id, Ord v) => HasRules (TermF id) v (NarradarTRS id v) where
  rules(TRS       rr _)     = toList rr
  rules(PrologTRS rr _)     = toList $ mconcat (Map.elems rr)
  rules(DPTRS     rr _ _ _) = elems rr

instance Ord id => HasSignature (NarradarTRS id v) where
    type SignatureId (NarradarTRS id v) = id -- SignatureId [Rule (TermF id) v]
    getSignature (TRS         _ sig) = sig
    getSignature (PrologTRS   _ sig) = sig
    getSignature (DPTRS   _ _ _ sig) = sig

instance (Ord id, Ord v) => IsTRS (TermF id) v (NarradarTRS id v) where
  tRS  rr = TRS (Set.fromList rr) (getSignature rr)

instance (Ord id, Ord v) => GetVars v (NarradarTRS id v) where getVars = getVars . rules

instance (Ord id, Ord v) => GetFresh (TermF id) v (NarradarTRS id v) where
    getFreshM (TRS rr sig) = getFresh (toList rr) >>= \rr' -> return (TRS (Set.fromDistinctAscList rr') sig)
    getFreshM (PrologTRS (unzip . Map.toList -> (i, rr)) sig) =
        getFresh rr >>= \rr' -> return (PrologTRS (Map.fromListWith mappend (zip i rr')) sig)
    getFreshM (DPTRS dps_a g uu sig) = getFresh (elems dps_a) >>= \dps' ->
                                       let dps_a' = listArray (bounds dps_a) dps'
                                       in return (DPTRS dps_a' g uu sig)
-- -------------------
-- Narradar instances
-- -------------------

instance (Ord id, Ord v) => Size (NarradarTRS id v) where size = F.sum . fmap size . rules

instance (Ord id, Ord v, ICap (TermF id) v [Rule (TermF id) v]) => ICap (TermF id) v (NarradarTRS id v) where
  icap trs = icap (rules trs)

instance (Ord id, Ord v) => ApplyAF (NarradarTRS id v) id where
    apply af (PrologTRS rr _) = prologTRS' ((Map.map . Set.map) (AF.apply af) rr)
    apply af trs@TRS{}        = tRS$ AF.apply af <$$> rules trs
    apply af (DPTRS a g uu _) = dpTRS' (AF.apply af <$$> a) g uu

-- ------------
-- Constructors
-- ------------
mkTRS :: (Ord id, Ord v) => [RuleN id v] -> NarradarTRS id v
mkTRS = tRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS ::  (RemovePrologId id, Ord id, Ord v) => [(WithoutPrologId id, RuleN id v)] -> NarradarTRS id v
prologTRS rr = prologTRS' (Map.fromListWith mappend $ map (second Set.singleton) rr)

prologTRS' :: (RemovePrologId id, Ord id, Ord v) => Map (WithoutPrologId id) (Set(RuleN id v)) -> NarradarTRS id v
prologTRS' rr = PrologTRS rr (getSignature rr)

narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)


-- | Assumes that the rules have already been renamed apart
dpTRS :: ( t ~ TermF (SignatureId trs)
         , SignatureId trs ~ Identifier a
         , Enum v, Ord a
         , HasRules t v trs, HasSignature trs, GetFresh t v trs, GetVars v trs, IsTRS t v trs
         , IsDPProblem typ, IUsableRules t v (typ, trs), ICap t v (typ, trs)
         ) =>
         typ -> trs -> trs -> Graph -> NarradarTRS (SignatureId trs) v
dpTRS typ trs dps edges = DPTRS dps_a edges unifs (getSignature dps)
    where dps_a   = listArray (0, length (rules dps) - 1) (rules dps)
          unifs   = runIcap dps (computeDPUnifiers typ trs dps)

dpTRS' dps edges unifiers = DPTRS dps edges unifiers (getSignature $ elems dps)

-- ----------
-- Functions
-- ----------

mapNarradarTRS :: (Ord (Term t v), Ord (Term t' v), Foldable t', HasId t') =>
                  (Term t v -> Term t' v) -> NarradarTRSF (Term t v) -> NarradarTRSF (Term t' v)
mapNarradarTRS f (TRS rr sig) = let rr' = Set.map (fmap f) rr in TRS rr' (getSignature rr')
mapNarradarTRS f (PrologTRS rr sig) = error "mapNarradarTRS: PrologTRS - sorry, can't do it"
                                  -- prologTRS (Map.mapKeys f' $ Map.map (fmap f) rr)where f' id = let id' = f (term
mapNarradarTRS f (DPTRS rr g (u1 :!: u2) _) = let rr' = fmap2 f rr
                                              in DPTRS rr' g (fmap3 f u1 :!: fmap3 f u2) (getSignature $ A.elems rr')

isDPTRS :: NarradarTRSF a -> Bool
isDPTRS DPTRS{} = True; isDPTRS _ = False

refreshRules :: (Traversable t, MonadEnv t (Either Var Var) m, MonadFresh v m, v ~ Var) => [Rule t v] -> m [Rule t v]
refreshRules rr = mapM2 (freshWith leftName) rr where leftName (Var n _) (Var _ i) = Var n i

restrictDPTRS :: Ord id => NarradarTRS id v -> [Int] -> NarradarTRS id v
restrictDPTRS (DPTRS dps gr (unif :!: unifInv) _) indexes = DPTRS dps' gr' unif' (getSignature $ elems dps')
  where
   newIndexes = Map.fromList (zip indexes [0..])
   nindexes   = length indexes -1
   dps'       = extractIxx dps indexes `asTypeOf` dps
   gr'        = A.amap (catMaybes . map (`Map.lookup` newIndexes)) (extractIxx gr indexes)
   extractIxx arr nodes = A.listArray (0, length nodes - 1) [arr A.! n | n <- nodes]
   unif' = (reindexArray unif :!: reindexArray unifInv)
   reindexArray arr =
           A.array ( (0,0), (nindexes, nindexes) )
                   [ ( (x',y'), sigma) | ((x,y),sigma) <- A.assocs arr
                                       , Just x' <- [Map.lookup x newIndexes]
                                       , Just y' <- [Map.lookup y newIndexes]]

dpUnify, dpUnifyInv :: NarradarTRSF (Term t v) -> Int -> Int -> Maybe (Substitution t v)
dpUnify    (DPTRS _ _ (unifs :!: _) _) l r = unifs ! (r,l)
dpUnifyInv (DPTRS _ _ (_ :!: unifs) _) l r = unifs ! (r,l)

rulesArray :: NarradarTRSF (Term t v) -> A.Array Int (Rule t v)
rulesArray (DPTRS dps _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

rulesGraph :: NarradarTRSF a -> Graph
rulesGraph (DPTRS _ g _ _) = g
rulesGraph _ = error "rulesGraph: only DP TRSs carry the dependency graph"


computeDPUnifiers :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , Enum v, Ord v, Ord term, Unify t
                     , IUsableRules t v (typ, trs), ICap t v (typ, trs)
                     , HasRules t v trs, IsTRS t v trs, GetFresh t v trs, GetVars v trs
                     , MonadFresh v m) =>
                     typ -> trs -> trs -> m(unif :!: unif)
--computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers typ trs dps = do
   trs_f <- getFresh trs
   let p_f = (typ, trs_f)

   u_rr <- listArray (0,ldps) `liftM` P.sequence [snd `liftM` iUsableRulesM p_f [r] | _:->r <- the_dps]

   rhss'<- P.mapM (\(_:->r) -> icap p_f r) (rules dps)
   unif <- runListT $ do
                (x, r')      <- liftL $ zip [0..] rhss'
                (y, l :-> _) <- liftL $ zip [0..] the_dps
                let unifier = unify l r'
                return ((x,y), unifier)
   unifInv <- runListT $ do
                (x, _ :-> r) <- liftL $ zip [0..] the_dps
                (y, l :-> _) <- liftL $ zip [0..] the_dps
                let p_inv = (map swapRule . rules) (u_rr ! x)
                l' <- lift (getFresh l >>= icap p_inv)
                let unifier = unify l' r
                return ((x,y), unifier)

   return(   array ( (0,0), (ldps,ldps) ) unif
         :!: array ( (0,0), (ldps,ldps) ) unifInv)
 where
   the_dps = rules dps
   liftL = ListT . return
   ldps  = length the_dps - 1

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

-- -------------
-- Sanity Checks
-- -------------
isValidUnif :: ( p   ~ DPProblem typ
               , trs ~ NarradarTRS id v
               , t   ~ TermF id
               , Ord v, Ord id, Enum v
               , Traversable p, IsDPProblem typ
               , ICap t v (p trs)
               ) => p trs -> Bool
isValidUnif p@(getP -> DPTRS dps _ (unif :!: _) _) =
    and $ runIcap p $ runListT $ do
         (x, _ :-> r) <- liftL $ A.assocs dps
         (y, l :-> _) <- liftL $ A.assocs dps
         r' <- getFresh r >>= icap p
         return (unifies l r' == isJust (unif A.! (x,y)))
  where
    liftL = ListT . return

isValidUnif _ = True
