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
import Data.Typeable
import Prelude as P hiding (concatMap, (.), id)

import qualified Data.Term as Family

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
import Narradar.Framework.Ppr as Ppr hiding ((<>))
import Narradar.Utils hiding (O)

import qualified Data.Id.Family as Family
import qualified Data.Rule.Family as Family
import qualified Data.Term.Family as Family
import qualified Data.Var.Family as Family

import Debug.Hoed.Observe

type FrameworkTRS trs =
  ( IsTRS trs, HasSignature trs, HasRules trs, GetFresh trs, GetVars trs, Observable trs
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
  , IUsableRules p trs
  , NeededRules p trs
  , ICap (p, trs)
  , FrameworkTRS trs
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

data Comparable where Comparable :: (Typeable a, Eq a) => a -> Comparable deriving (Typeable)
instance Eq Comparable where Comparable a == Comparable b = cast a == Just b

data NarradarTRSF a where
    TRS       :: (HasId t, Ord (Term t v)) =>
                 { rulesS :: Set (Rule t v)
                 , sig    :: Signature (Family.Id t)
                 } -> NarradarTRSF (Rule t v)

    PrologTRS :: (HasId t, RemovePrologId (Family.Id t), Ord (Term t v)) =>
                 { rulesByClause :: Map (WithoutPrologId (Family.Id t)) (Set (Rule t v))
                 , sig           :: Signature (Family.Id t)
                 } -> NarradarTRSF (Rule t v)

    DPTRS     :: (HasId t, Ord (Term t v)) =>
                 { typ       :: Comparable
                 , dpsA      :: !(Array Int (Rule t v))
                 , rulesUsed :: NarradarTRSF (Rule t v)
                 , depGraph  :: Graph
                 , unifiers  :: Two (Unifiers t v)
                 , sig       :: Signature (Family.Id t)
                 } -> NarradarTRSF (Rule t v)

      -- | Used in very few places instead of TRS, when the order of the rules is important
    ListTRS :: (HasId t, Ord (Term t v)) => [Rule t v] -> Signature (Family.Id t) -> NarradarTRSF (Rule t v)

    deriving Typeable

type instance Family.Id     (NarradarTRSF a) = Family.Id a
type instance Family.Rule   (NarradarTRSF a) = Family.Rule a
type instance Family.Var    (NarradarTRSF a) = Family.Var a
type instance Family.TermF  (NarradarTRSF a) = Family.TermF a

type Unifiers t v = Array (Int,Int) (Maybe (Two(Substitution t v)))
type NarradarTRS t v = NarradarTRSF (Rule t v)
type NTRS id = NarradarTRS (TermF id) Var

instance Eq (NarradarTRS t v) where
    TRS rr1 _       == TRS rr2 _       = rr1 == rr2
    PrologTRS rr1 _ == PrologTRS rr2 _ = rr1 ==  rr2
    DPTRS _ rr1 _ _ _ _ == DPTRS _ rr2 _ _ _ _ = rr1 == rr2
    ListTRS rr1 _   == ListTRS rr2 _   = Set.fromList rr1 == Set.fromList rr2
    ListTRS rr1 _   == TRS rr2 _       = Set.fromList rr1 == rr2
    TRS rr1 _       == ListTRS rr2 _   = rr1 == Set.fromList rr2
    rr1@DPTRS{dpsA} == rr2@TRS{rulesS} = Set.fromList (elems dpsA) == rulesS
    rr1@TRS{rulesS} == rr2@DPTRS{dpsA} = rulesS == Set.fromList (elems dpsA)
 -- The rest of cases should not occurr at runtime

instance Ord (NarradarTRS t v) where
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS _ rr1 _ _ _ _) (DPTRS _ rr2 _ _ _ _) = compare rr1 rr2
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
    mappend (DPTRS _ dp1 _  _ _ _) (DPTRS _ dp2 _ _ _ _) =
       let dps = elems dp1 `mappend` elems dp2
       in mkTRS dps
    mappend (TRS (Set.null -> True) _) trs = trs
    mappend trs (TRS (Set.null -> True) _) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (Pretty v, Pretty (t(Term t v))) => Pretty (NarradarTRS t v) where
    pPrint trs@TRS{}       = vcat $ map pPrint $ rules trs
    pPrint trs@DPTRS{}     = vcat $ map pPrint $ rules trs
    pPrint trs@PrologTRS{} = vcat $ map pPrint $ rules trs
    pPrint (ListTRS  rr _) = vcat $ map pPrint rr

instance (NFData (t(Term t v)), NFData (Family.Id t), NFData v) => NFData (NarradarTRS t v) where
    rnf (TRS rr sig) = rnf rr `seq` rnf sig `seq` ()
    rnf (DPTRS typ dps rr g unif sig) = typ `seq` rnf dps `seq` rnf rr `seq` rnf sig `seq` rnf unif `seq` rnf sig
--    rnf (PrologTRS rr sig)    = rnf rr

instance (NFData a, NFData b) => NFData (a :!: b) where
    rnf (a :!: b) = rnf a `seq` rnf b `seq` ()

instance Observable1 NarradarTRSF where
  observer1 (ListTRS rr sig) = send "ListTRS" (return (`ListTRS` sig) << rr)
  observer1 (TRS rr sig) = send "TRS" (return (`TRS` sig) << rr)
  observer1 (DPTRS typ dpsA ru dg unif sig)
     = send "DPTRS" (return (\dpsA -> DPTRS typ dpsA ru dg unif sig) << dpsA)

isNarradarTRS :: NarradarTRS t v -> NarradarTRS t v
isNarradarTRS = id


isNarradarTRS1 :: NarradarTRS (t id) v -> NarradarTRS (t id) v
isNarradarTRS1 = id

listTRS :: (HasId t, Foldable t, Ord (Term t v)) => [Rule t v] -> NarradarTRS t v
listTRS rr = ListTRS rr (getSignature rr)

narradarTRStoSet :: NarradarTRS t v -> Set (Rule t v)
narradarTRStoSet TRS{..} = rulesS
narradarTRStoSet (ListTRS rr _) = Set.fromList rr

-- ------------------------------
-- Data.Term framework instances
-- ------------------------------
instance HasRules (NarradarTRS t v) where
  rules(TRS       rr _)       = toList rr
  rules(PrologTRS rr _)       = toList $ mconcat (Map.elems rr)
  rules(DPTRS   _ rr _ _ _ _) = elems rr
  rules(ListTRS   rr _)       = rr

instance Ord (Family.Id t) => HasSignature (NarradarTRS t v) where
    getSignature (TRS           _ sig) = sig
    getSignature (PrologTRS     _ sig) = sig
    getSignature (DPTRS _ _ _ _ _ sig) = sig
    getSignature (ListTRS rr      sig) = sig

instance (Ord (Term t v), Foldable t, HasId t) => IsTRS (NarradarTRS t v) where
  tRS  rr = TRS (Set.fromList rr) (getSignature rr)

instance (Ord v, Functor t, Foldable t) => GetVars (NarradarTRS t v) where getVars = getVars . rules

instance (Traversable t, Ord v, GetFresh (Set (Rule t v))) => GetFresh (NarradarTRS t v) where
    getFreshM (TRS rr sig) = getFresh (toList rr) >>= \rr' -> return (TRS (Set.fromDistinctAscList rr') sig)
    getFreshM (ListTRS rr sig) = getFresh rr >>= \rr' -> return (ListTRS rr' sig)
    getFreshM (PrologTRS (unzip . Map.toList -> (i, rr)) sig) =
        getFresh rr >>= \rr' -> return (PrologTRS (Map.fromListWith mappend (zip i rr')) sig)
    getFreshM (DPTRS typ dps_a rr g uu sig) = getFresh (elems dps_a) >>= \dps' ->
                                       let dps_a' = listArray (bounds dps_a) dps'
                                       in return (DPTRS typ dps_a' rr g uu sig)
-- -------------------
-- Narradar instances
-- -------------------

class IUsableRules typ (NTRS id) => NUsableRules typ id
instance IUsableRules typ (NTRS id) => NUsableRules typ id

class NeededRules typ (NTRS id) => NNeededRules typ id
instance NeededRules typ (NTRS id) => NNeededRules typ id

class ICap (typ, NTRS id) => NCap typ id
instance ICap (typ, NTRS id) => NCap typ id


instance (Functor t, Foldable t) => Size (NarradarTRS t v) where size = F.sum . fmap size . rules

instance (Ord (Term t v), ICap [Rule t v]) => ICap (NarradarTRS t v) where
  icapO o trs = icapO o (rules trs)

instance (Ord (Term t v), Foldable t, ApplyAF (Term t v)) => ApplyAF (NarradarTRS t v) where
  apply af (PrologTRS rr _)    = prologTRS' ((Map.map . Set.map) (AF.apply af) rr)
  apply af trs@TRS{}           = tRS$ AF.apply af <$$> rules trs
  apply af (DPTRS _ a rr g uu _) = tRS (AF.apply af <$$> toList a) -- cannot recreate the graph without knowledge of the problem type
  apply af (ListTRS rr _)      = let rr' = AF.apply af <$$> rr in ListTRS rr' (getSignature rr')

instance (Functor t, Foldable t, Ord v) =>  ExtraVars (NarradarTRS t v) where
  extraVars (TRS rr _)        = extraVars rr
  extraVars (PrologTRS rr _)  = extraVars rr
  extraVars (DPTRS _ a _ _ _ _) = extraVars (A.elems a)

instance (ICap (typ, NarradarTRS t v), Ord (Term t v), Foldable t, HasId t) => ICap (typ, [Rule t v]) where
  icapO o (typ, p) = icapO o (typ, mkTRS p)

-- ------------
-- Constructors
-- ------------
mkTRS :: (Ord(Term t v), Foldable t, HasId t) => [Rule t v] -> NarradarTRS t v
mkTRS = tRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS ::  (Ord (Term t v), RemovePrologId (Family.Id t), Foldable t, HasId t) =>
              [(WithoutPrologId (Family.Id t), Rule t v)] -> NarradarTRS t v
prologTRS rr = prologTRS' (Map.fromListWith mappend $ map (second Set.singleton) rr)

prologTRS' :: (Ord (Term t v), RemovePrologId (Family.Id t), Foldable t, HasId t) =>
              Map (WithoutPrologId (Family.Id t)) (Set(Rule t v)) -> NarradarTRS t v
prologTRS' rr = PrologTRS rr (getSignature rr)

narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)

dpTRS :: ( FrameworkN0 typ t v
         ) =>
         typ -> NarradarTRS t v -> NarradarTRS t v -> NarradarTRS t v
dpTRS = dpTRSO nilObserver

-- | Assumes that the rules have already been renamed apart
dpTRSO :: ( FrameworkN0 typ t v
         ) =>
         Observer -> typ -> NarradarTRS t v -> NarradarTRS t v -> NarradarTRS t v

dpTRSO (O o oo) typ trs dps = dpTRS' typ dps_a (tRS trs') unifs
    where
      (trs',dps') = runVariant $ do
        trs' <- mapM getFresh $ rules trs
        dps' <- mapM getFresh $ snub (rules dps)
        return (trs', dps')
      dps_a   = listArray (0, length dps' - 1) dps'
      unifs   = runIcap (trs' ++ dps')
                        (oo "computeDirectUnifiers" computeDPUnifiersO typ (listTRS trs')
                                                                           (listTRS dps'))


dpTRS' :: ( Eq typ, Typeable typ, Foldable t, HasId t, Ord (Term t v)) =>
         typ -> Array Int (Rule t v) -> NarradarTRS t v -> Two (Unifiers t v) -> NarradarTRS t v
dpTRS' typ dps rr unifiers = DPTRS (Comparable typ) dps rr (getIEDGfromUnifiers unifiers) unifiers (getSignature $ elems dps)


-- ----------
-- Functions
-- ----------

mapNarradarTRS :: (Ord (Term t v), Ord (Term t' v), Foldable t', HasId t') =>
                  (Term t v -> Term t' v) -> NarradarTRS t v -> NarradarTRS t' v
mapNarradarTRS f (TRS rr sig) = let rr' = Set.map (fmap f) rr in TRS rr' (getSignature rr')
mapNarradarTRS f (PrologTRS rr sig) = error "mapNarradarTRS: PrologTRS - sorry, can't do it"
                                  -- prologTRS (Map.mapKeys f' $ Map.map (fmap f) rr)where f' id = let id' = f (term
mapNarradarTRS f (DPTRS typ dps rr g uu _)
   = let dps' = fmap2 f dps
         rr'  = mapNarradarTRS f rr
     in DPTRS typ dps' rr' g (fmap5 f uu) (getSignature $ A.elems dps')

mapNarradarTRS' :: (Ord (Term t v), Ord (Term t' v), Foldable t', HasId t') =>
                   (Term t v -> Term t' v) -> (Rule t v -> Rule t' v) -> NarradarTRS t v -> NarradarTRS t' v
mapNarradarTRS' _ fr (TRS rr sig) = let rr' = Set.map fr rr in TRS rr' (getSignature rr')
mapNarradarTRS' _ fr (PrologTRS rr sig) = error "mapNarradarTRS': PrologTRS - sorry, can't do it"
                                  -- prologTRS (Map.mapKeys f' $ Map.map (fmap f) rr)where f' id = let id' = f (term
mapNarradarTRS' ft fr (DPTRS typ dps rr g uu _)
   = let dps' = fmap fr dps
         rr'  = mapNarradarTRS' ft fr rr
     in DPTRS typ dps' rr' g (fmap5 ft uu) (getSignature $ A.elems dps')

filterNarradarTRS :: Foldable t => (Rule t v -> Bool) -> NarradarTRS t v -> NarradarTRS t v
filterNarradarTRS p (TRS rr sig) = mkTRS (filter p (Set.toList rr))

isDPTRS :: NarradarTRSF a -> Bool
isDPTRS DPTRS{} = True; isDPTRS _ = False

restrictTRS :: Foldable t => NarradarTRS t v -> [Int] -> NarradarTRS t v
restrictTRS (TRS rr _) indexes = let rr' = Set.fromList (selectSafe "restrictTRS 1" indexes (toList rr))
                                   in TRS rr' (getSignature rr')
restrictTRS (PrologTRS rr _) indexes = let rr'  = Map.fromList (selectSafe "restrictTRS 2" indexes (Map.toList rr))
                                           sig' = getSignature (Map.elems rr')
                                       in PrologTRS rr' (getSignature rr')

restrictTRS (DPTRS typ dps rr gr unif _) indexes
  = DPTRS typ dps' rr gr' unif' (getSignature $ elems dps')
  where
   newIndexes = Map.fromList (zip indexes [0..])
   nindexes   = length indexes -1
   dps'       = extractIxx dps indexes `asTypeOf` dps
   gr'        = A.amap (catMaybes . map (`Map.lookup` newIndexes)) (extractIxx gr indexes)

   extractIxx :: Array Int a -> [Int] -> Array Int a
   extractIxx arr nodes = A.listArray (0, length nodes - 1) [safeAt "restrictTRS" arr n | n <- nodes]

   unif' = (fmap reindexArray unif)
   reindexArray arr =
           A.array ( (0,0), (nindexes, nindexes) )
                   [ ( (x',y'), sigma) | ((x,y),sigma) <- A.assocs arr
                                       , Just x' <- [Map.lookup x newIndexes]
                                       , Just y' <- [Map.lookup y newIndexes]]

dpUnify, dpUnifyInv :: NarradarTRS t v -> Int -> Int -> Maybe (Substitution t v)
dpUnify    (DPTRS _ _ _ _ (Two unifs _) _) l r = item1 <$> safeAt "dpUnify" unifs (r,l)
dpUnifyInv (DPTRS _ _ _ _ (Two _ unifs) _) l r = item1 <$> safeAt "dpUnifyInv" unifs (r,l)

rulesArray :: NarradarTRS t v -> A.Array Int (Rule t v)
rulesArray (DPTRS _ dps _ _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

rulesGraph :: NarradarTRSF a -> Graph
rulesGraph (DPTRS _ _ _ g _ _) = g
rulesGraph _ = error "rulesGraph: only DP TRSs carry the dependency graph"


computeDPUnifiers :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , t ~ Family.TermF trs
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , Rule t v ~ Family.Rule trs
                     , FrameworkProblem0 typ trs
                     , Observable1 m
                     , MonadVariant m) =>
                     typ -> trs -> trs -> m(Two unif)
computeDPUnifiers x = computeDPUnifiersO nilObserver x

computeDPUnifiersO :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , t ~ Family.TermF trs
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , Rule t v ~ Family.Rule trs
                     , FrameworkProblem0 typ trs
                     , Observable1 m
                     , MonadVariant m) =>
                     Observer -> typ -> trs -> trs -> m(Two unif)
computeDPUnifiersO o typ trs dps = do
   unif    <- computeDirectUnifiersO  o (typ, trs) dps
   unifInv <- computeInverseUnifiersO o (typ, trs) dps

   return (Two unif unifInv)


computeDirectUnifiers :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , t ~ Family.TermF trs
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , Rule t v ~ Family.Rule trs
                     , Ord v, Unify t
                     , HasRules trs, GetFresh trs
                     , ICap (typ, trs)
                     , Pretty (Term t v), Pretty v
                     , Observable (Term t v), Observable trs, Observable typ
                     , MonadVariant m
                     , Observable v
                     , Observable1 m
                     , Observable1 t) =>
                     (typ, trs) -> trs -> m unif
computeDirectUnifiers x = computeDirectUnifiersO nilObserver x

computeDirectUnifiersO :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , t ~ Family.TermF trs
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , Rule t v ~ Family.Rule trs
                     , Ord v, Unify t
                     , HasRules trs, GetFresh trs
                     , ICap (typ, trs)
                     , Pretty (Term t v), Pretty v
                     , Observable (Term t v), Observable trs, Observable typ
                     , MonadVariant m
                     , Observable v
                     , Observable1 m
                     , Observable1 t) =>
                     Observer -> (typ, trs) -> trs -> m unif
computeDirectUnifiersO (O o oo) p_f (rules -> the_dps) =
   let doOne (O o _) (x, s:->t) (y, u:->v) = do
         (_:->t'', u1) <- runMEnv $ o "getFreshM"  getFreshM (s:->t)
         (u':->v', u2) <- runMEnv $ o "getFreshM2" getFreshM (u:->v)
         t'            <- oo "icap" icapO p_f [s,u] t''
         let sigma = o "unify" unify u' t'
                -- pprTrace (vcat [text "unify" <+> (u <+> text "with" <+> t')
                --                ,parens (text "icap" <+> (rules(snd p_f) $$ t))
                --                ,equals <+> unifier]) (return ())
         return ((x,y), fmap (\sigma -> Two (u1<>sigma) (u2<>sigma)) sigma)
       ldps  = length the_dps - 1
   in do
     unif <- runListT $ do
                rule1 <- liftL $ zip [0..] the_dps
                rule2 <- liftL $ zip [0..] the_dps
                oo "doOne" doOne rule1 rule2
     return $ array ( (0,0), (ldps, ldps) ) unif


computeInverseUnifiersO :: forall unif typ trs t v term m.
                     ( unif ~ Unifiers t v
                     , term ~ Term t v
                     , v ~ Family.Var m
                     , v ~ Family.Var trs
                     , t ~ Family.TermF trs
                     , Rule t v ~ Family.Rule trs
                     , FrameworkProblem0 typ trs
                     , MonadVariant m
                     , Observable1 m) =>
                     Observer -> (typ, trs) -> trs -> m unif
--computeInverseUnifiers _ _ | trace "computeInverseUnifiers" False = undefined
computeInverseUnifiersO (O o oo) (typ, trs) dps = do
   let ldps  = length (rules dps) - 1

   unif <- runListT $ do
                (x, s :-> t) <- liftL $ zip [0..] (rules dps)
                (y, u :-> v) <- liftL $ zip [0..] (rules dps)
                u_rr <- {-o "usableRules"-} iUsableRulesM typ trs dps [s,u] [t]
                let p_inv = map swapRule (rules u_rr)
                (s':->t', u1) <- lift (runMEnv $ getFreshM (s:->t))
                (u':->_,  u2) <- lift (runMEnv $ getFreshM (u:->v))
                u'' <- lift ({-o"icap"-} icap (typ, tRS p_inv `asTypeOf` trs) [] u')
                let sigma = {-o "unify"-} unify u'' t'
--                pprTrace (text "unify" <+> l' <+> parens (text "icap" <+> p_inv <+> l)
--                          <+> text "with" <+> r <+> equals <+> unifier) (return ())
                return ((x,y), fmap (\sigma -> Two (u1<>sigma) (u2<>sigma)) sigma)
   return $ array ((0,0), (ldps,ldps)) unif


getIEDGfromUnifiers (Two unif unifInv) = G.buildG (m,n) the_edges where
  the_edges = [ xy | (xy, Just _) <- A.assocs unif
                   , isJust (safeAt "getIEDGFromUnifiers" unifInv xy)
                   ]
  ((m,_),(n,_)) = bounds unif

getEDGfromUnifiers (Two unif _) = G.buildG (m,n) the_edges where
  the_edges = [ xy | (xy, Just _) <- A.assocs unif
                   ]
  ((m,_),(n,_)) = bounds unif


instance Pretty (Unifiers t v) where pPrint = pPrint . amap (maybe "N" (const "Y"))
