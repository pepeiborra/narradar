{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.TRS where

import Control.Applicative
import Control.Arrow (second, (***))
import Control.Monad (liftM)
import Data.Array.IArray as A
import Data.Graph (Graph)
import Data.Foldable as F (toList, sum, foldMap)
import Data.Maybe (catMaybes)
import Data.Monoid
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Text.PrettyPrint
import Prelude hiding (concatMap)

import Narradar.Types.ArgumentFiltering (ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Term hiding ((!))
import Narradar.Types.Var
import Narradar.Utils.Convert
import Narradar.Utils.Ppr
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

data NarradarTRSF id t v a where
    TRS       :: Set a                                                  -> Signature id -> NarradarTRSF id t v a
    PrologTRS :: (RemovePrologId id) => Map (WithoutPrologId id) (Set a)-> Signature id -> NarradarTRSF id t v a
    DPTRS     :: Array Int a -> !Graph -> Unifiers t v :!: Unifiers t v -> Signature id -> NarradarTRSF id t v a

type NarradarTRS id v = NarradarTRSF id (TermF id) v (RuleN id v)

type Unifiers t v = Array (Int,Int) (Maybe (Substitution t v))

instance (Ord id, Ord v) => GetVars v (NarradarTRS id v) where getVars = getVars . rules

instance (Ord id, Ord v) => Eq (NarradarTRS id v) where trs1 == trs2 = rules trs1 == rules trs2

instance (Ord id, Ord v) => Ord (NarradarTRS id v) where
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _ _) (DPTRS rr2 _ _ _) = compare rr1 rr2
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT

instance (Ord id, Ord v) => HasRules (TermF id) v (NarradarTRS id v) where
  rules(TRS       rr _)     = toList rr
  rules(PrologTRS rr _)     = toList $ mconcat (Map.elems rr)
  rules(DPTRS     rr _ _ _) = elems rr
instance (Ord id, Ord v) => IsTRS (TermF id) v (NarradarTRS id v) where
  tRS  rr = TRS (Set.fromList rr) (getSignature rr)

instance (Ord id, Ord v) => Size (NarradarTRS id v) where size = F.sum . fmap size . rules


instance (Convert (WithoutPrologId id) (WithoutPrologId id'), RemovePrologId id',
          Convert (TermN id v) (TermN id' v'), Ord id, Ord id', Ord v, Ord v') =>
          Convert (NarradarTRS id v) (NarradarTRS id' v') where
    convert(PrologTRS rr _) = prologTRS'  (Map.fromListWith mappend $ map (convert *** Set.map convert) $ Map.toList rr)
    convert (TRS rr _)      = narradarTRS (map convert$ toList rr)

{-
instance (Convert id id', Convert (TermN id v) (TermN id' v'), Ord id, Ord id', Ord v') =>
          Convert (NarradarTRS id v) (NarradarTRS id' v') where
    convert(PrologTRS rr sig) = error "convert: unexpected - spotted a PrologTRS with no PrologIds" -- prologTRS' (Map.fromList [ (convert k, convert rr) | (k,rr) <- Map.toList rr])
    convert (TRS rr _)      = narradarTRS (map convert$ toList rr)
-}

instance (Ord id, Ord v) => GetFresh (TermF id) v (NarradarTRS id v) where
    getFreshM (TRS rr sig) = getFresh (toList rr) >>= \rr' -> return (TRS (Set.fromDistinctAscList rr') sig)
    getFreshM (PrologTRS (unzip . Map.toList -> (i, rr)) sig) =
        getFresh rr >>= \rr' -> return (PrologTRS (Map.fromListWith mappend (zip i rr')) sig)
--          where runFresh m = evalState m [toEnum (1+maximum(0 : fromEnum <$> getVars rr)) ..]
    getFreshM (DPTRS dps_a g uu sig) = getFresh (elems dps_a) >>= \dps' ->
                                       let dps_a' = listArray (bounds dps_a) dps'
                                       in return (DPTRS dps_a' g uu sig)

mkTRS :: (Ord id, Ord v) => [RuleN id v] -> NarradarTRS id v
mkTRS = tRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS ::  (RemovePrologId id, Ord id, Ord v) => [(WithoutPrologId id, RuleN id v)] -> NarradarTRS id v
prologTRS rr = prologTRS' (Map.fromListWith mappend $ map (second Set.singleton) rr)

prologTRS' :: (RemovePrologId id, Ord id, Ord v) => Map (WithoutPrologId id) (Set(RuleN id v)) -> NarradarTRS id v
prologTRS' rr = PrologTRS rr (getSignature rr)

narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)

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

dpUnify    (DPTRS _ _ (unifs :!: _) _) l r = unifs ! (r,l)
dpUnifyInv (DPTRS _ _ (_ :!: unifs) _) l r = unifs ! (r,l)

rulesArray (DPTRS dps _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

instance Ord id => HasSignature (NarradarTRS id v) id where
    getSignature (TRS         _ sig) = sig
    getSignature (PrologTRS   _ sig) = sig
    getSignature (DPTRS   _ _ _ sig) = sig


instance HasSignature [a] id => HasSignature (Set a)   id where getSignature = getSignature . Set.toList
instance HasSignature [a] id => HasSignature (Map k a) id where getSignature = getSignature . Map.elems
instance (Ord id, Monoid a, HasSignature a id) => HasSignature [a] id where getSignature = getSignature . mconcat
instance (Ord a, GetFresh t v a) => GetFresh t v (Set a) where getFreshM = liftM Set.fromList . getFreshM . Set.toList
instance HasRules t v a => HasRules t v (Set   a) where rules = foldMap rules . toList
instance HasRules t v a => HasRules t v (Map k a) where rules = foldMap rules . Map.elems

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


instance (Ord id, Ord v) => ApplyAF (NarradarTRS id v) id where
    apply af (PrologTRS rr _) = prologTRS' ((Map.map . Set.map) (apply af) rr)
    apply af trs@TRS{}        = tRS$ apply af <$$> rules trs
    apply af trs@DPTRS{}      = tRS$ apply af <$$> rules trs
