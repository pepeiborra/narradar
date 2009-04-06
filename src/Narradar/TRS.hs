{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Narradar.TRS where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.MonadSupply
import Data.Array.IArray as A
import Data.Graph (Graph)
import Data.Foldable as F (foldMap, toList)
import Data.List ((\\))
import Data.Maybe (catMaybes)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Text.PrettyPrint

import TRS hiding (Ppr, ppr, unify, unifies, apply, (!))
import qualified TRS
import Narradar.ArgumentFiltering (apply, ApplyAF(..))
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPIdentifiers
import Narradar.Labellings
import Narradar.ProblemType
import Narradar.Unify
import Narradar.Utils
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Syntax (Ident)

type DP a = Rule a

-- --------------------
-- TRSs in our setting
-- --------------------

{-
TRS and PrologTRS are straightforward.
DPTRS contains additional payload to cache:
1) the graph 2) the unifiers between the pairs computed by the graph processor.
The unifiers are cached in a matrix (an (rhs,lhs) array) with the following layout

\ LHS|     |     |
 \   |pair1|pair2|
RHS\ |     |     |
------------------
pair1|_____|_____|
pair2|_____|_____|
.....|     |     |
-}

data NarradarTRS id f where
    TRS       :: (Ord id, TRSC f, T id :<: f) => Set (Rule f)                                 -> Signature id -> NarradarTRS id f
    PrologTRS :: (Ord id, TRSC f, T id :<: f) => Set (Ident, Rule f)                          -> Signature id -> NarradarTRS id f
    DPTRS     :: (Ord id, TRSC f, T id :<: f) => Array Int (Rule f) -> Graph -> (Unifiers f, Unifiers f) -> Signature id -> NarradarTRS id f

type Unifiers        f = Array (Int,Int) (Maybe (Subst f))

instance (Ord id, Ord (Term f), TRSC f, T id :<: f) => Ord (NarradarTRS id f) where
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BasicId) #-}
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BBasicId) #-}
    {-# off SPECIALIZE instance Ord(NarradarTRS LId BBasicLId) #-}
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _ _) (DPTRS rr2 _ _ _)   = compare rr1 rr2

instance (Ord id, T id :<: f, TRSC f) => TRS (NarradarTRS id f) id f where
    {-# SPECIALIZE instance TRS(NarradarTRS Id BasicId) Id BasicId #-}
    {-# SPECIALIZE instance TRS(NarradarTRS Id BBasicId) Id BBasicId #-}
    {-# off SPECIALIZE instance TRS(NarradarTRS LId BBasicLId) LId BBasicLId #-}
    rules(TRS       rr _)   = toList rr
    rules(PrologTRS rr _)   = map snd (toList rr)
    rules(DPTRS     rr _ _ _) = elems rr
    tRS = narradarTRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS :: forall id f. (Ord id, TRSC f, T id :<: f) => [(Ident, Rule f)] -> NarradarTRS id f
prologTRS rr = prologTRS' (Set.fromList rr)

prologTRS' :: forall id f. (Ord id, TRSC f, T id :<: f) => Set(Ident, Rule f) -> NarradarTRS id f
prologTRS' rr = PrologTRS rr (getSignature (snd <$> toList rr))

{-# SPECIALIZE narradarTRS ::  [Rule BBasicId] -> NarradarTRS Id BBasicId #-}
narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)
--dpTRS :: (T id :<: d) => ProblemType id -> NarradarTRS id f -> [DP f] -> Graph -> NarradarTRS id f
dpTRS typ trs dps edges = dpTRS' typ trs dps' edges
  where dps' = listArray (0, length dps - 1) (refreshRules [0..] dps)

-- | Assumes that the rules have already been renamed apart
--dpTRS' :: (T id :<: d) => ProblemType id -> NarradarTRS id f -> Array Int (DP f) -> Graph -> NarradarTRS id f
dpTRS' typ trs dps edges = DPTRS dps edges (computeDPUnifiers typ trs $ elems dps)
                                           (getSignature $ elems dps)

-- | Assumes that the rules have already been renamed apart
dpTRS'' dps edges unifiers = DPTRS dps edges unifiers (getSignature $ elems dps)

refreshRules ids  = (`runSupply'` ids) . mapM doRule where
        doRule r = do
          let vv = foldMap vars' r
          newvv <- replicateM (length vv) next
          return (replace (Prelude.zipWith leftName vv newvv) <$> r)

        leftName v1 i2 = (v1, var' (varName v1) i2)

        varName (open -> Just (Var n _)) = n
        varName _ = Nothing

--computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers :: (DPMark f, TRS trs id f, ApplyAF trs id, MonadPlus m, unif ~ Array (Int,Int) (m(Subst f)))=> ProblemType id -> trs -> [DP f] -> (unif,unif)
computeDPUnifiers typ trs dps =
     (array ( (0,0), (length dps -1 , length dps - 1) )
           [((x,y), unify' l (if x/=y then r' else head(variant' [r'] [l])))
              | (x, _ :-> r) <- zip [0..] dps
              , (y, l :-> _) <- zip [0..] dps
              , let r' = mbren (icap trs r) ]
     ,array ( (0,0), (length dps -1 , length dps - 1) )
           [((x,y), unify' r (if x/=y then l' else head(variant' [l'] [r])))
              | (x, _ :-> r) <- zip [0..] dps
              , (y, l :-> _) <- zip [0..] dps
              , let trs' = tRS (swapRule <$> mbUsableRules [r]) `asTypeOf` trs
              , let l' = ren(icap trs' l)])
   where
   (mbren, mbUsableRules) = if (isBNarrowing .|. isGNarrowing) typ
                              then (id,iUsableRules trs Nothing)
                              else (ren,const (rules trs))

restrictDPTRS (DPTRS dps gr (unif, unifInv) sig) indexes =
    DPTRS dps' gr' unif' sig `const` dps `const` indexes
  where
   newIndexes = Map.fromList (zip indexes [0..])
   nindexes   = length indexes -1
   dps'       = extractIxx dps indexes
   gr'        = A.amap (catMaybes . map (`Map.lookup` newIndexes)) (extractIxx gr indexes)
   extractIxx arr nodes = A.listArray (0, length nodes - 1) [arr A.! n | n <- nodes]
   unif' = (reindexArray unif, reindexArray unifInv)
   reindexArray arr =
           A.array ( (0,0), (nindexes, nindexes) )
                   [ ( (x',y'), sigma) | ((x,y),sigma) <- A.assocs arr
                                       , Just x' <- [Map.lookup x newIndexes]
                                       , Just y' <- [Map.lookup y newIndexes]]

dpUnify    (DPTRS _ _ (unifs,_) _) i j = unifs ! (i,j)
dpUnifyInv (DPTRS _ _ (_,unifs) _) i j = unifs ! (i,j)

rulesArray (DPTRS dps _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

instance Ord id => HasSignature (NarradarTRS id f) id where
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BasicId) Id #-}
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BBasicId) Id #-}
    {-# off SPECIALIZE instance HasSignature(NarradarTRS LId BBasicLId) LId #-}
    getSignature (TRS         _ sig) = sig
    getSignature (PrologTRS   _ sig) = sig
    getSignature (DPTRS   _ _ _ sig) = sig

instance (T id :<: f, Ord id, TRSC f) => Monoid (NarradarTRS id f) where
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BasicId) #-}
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BBasicId) #-}
    {-# off SPECIALIZE instance Monoid(NarradarTRS LId BBasicLId) #-}
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature (snd <$> toList rr))
    mappend (DPTRS r1 e1 _ _) (DPTRS r2 e2 _ _) =
       let rr = elems r1 `mappend` elems r2 in TRS (Set.fromList rr) (getSignature rr)
    mappend emptytrs trs | null (rules emptytrs) = trs
    mappend trs emptytrs | null (rules emptytrs) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (T id :<: f, Ord id, TRSC f) =>  Size (NarradarTRS id f) where size = sizeTRS

instance TRS.Ppr f      => Ppr (NarradarTRS id f) where
    ppr trs@TRS{} = vcat $ map ppr $ rules trs


instance (Ord id) => ApplyAF (NarradarTRS id f) id where
    {-# SPECIALIZE instance ApplyAF (NarradarTRS LPId BasicLPId) LPId #-}
    apply af (PrologTRS  cc sig) = let trs' = PrologTRS (Set.mapMonotonic (\(c,r) ->(c, apply af r)) cc) (getSignature $ rules trs') in trs'
    apply af trs@TRS{}           = tRS$ apply af <$$> rules trs
    apply af trs@DPTRS{}         = tRS$ apply af <$$> rules trs

-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, but we need to make GHC happy (avoid recursive module dependencies)

ren :: (Var :<: f, HashConsed f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

cap, icap :: forall trs f id. (Ord id, TRSC f, TRS trs id f) => trs -> Term f -> Term f
cap trs t = evalState (go t) freshvv where
  freshvv = map var [0..] \\ vars' t
  go (open -> Just (T (s::id) tt)) | isDefined trs t = next
                                   | otherwise       = term s <$> mapM go tt
  go v = return v
{-
-- Use unification instead of just checking if it is a defined symbol
-- This is not the icap defined in Rene Thiemann, as it does not integrate the REN function
icap' trs = runSupply . foldTermM go where
  go in_t | Just (T (f::id) tt) <- prj in_t, t <- inject in_t
       = if  any (unifies t . lhs) (rules trs) then var <$> next else return t
  go v = return (inject v)
                  -- In Rene Thiemann, icap inserts a fresh variable here in some cases
                  -- but unfortunately we lack a good infrastructure for doing this
-}
-- Top down definition, equivalent to the above Bottom-up (written in avoiding a type class style)
icap trs t = runSupply (go t) where
  go t@(In in_t) | Just (T (f::id) tt) <- open t
                 = do
      t' <- In <$> (go `T.mapM` in_t)
      if  any (unifies t' . lhs) (rules trs) then var <$> next else return t'
  go v = return v



capInv :: forall id f. (Ord id, T id :<: f, TRSC f) => NarradarTRS id f -> Term f -> Term f
capInv trs t
       | collapsing trs = var 0
       | Just (T (s::id) tt) <- open t
       = term s [if isDefined trs' t' then var i else t'
                       | (i,t') <- [0..] `zip` tt]
       | otherwise = t
  where trs' = tRS (swapRule <$> rules trs) :: NarradarTRS id f

collapsing trs = any (isVar.rhs) (rules trs)


-- ---------------------
-- Usable rules of a TRS
-- ---------------------

-- Assumes Innermost or Constructor Narrowing
-- TODO Extend to work with Q-narrowing to discharge those assumptions
iUsableRules :: (Ord id, TRSC f, TRS trs id f, AF.ApplyAF trs id, DPMark f) => trs -> Maybe (AF.AF_ id) -> [Term f] -> [Rule f]
iUsableRules trs Nothing = F.toList . go mempty where
--  usableRules acc t | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t@(In in_t):rest)
      | isVar t
      = go acc rest
      | rr   <- Set.fromList [r | r <- rules trs
                                , hIn (icap trs <$> in_t) `unifies` lhs r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])


iUsableRules trs (Just pi) = F.toList . go mempty . map(AF.apply pi) where
  pi_trs = AF.apply pi trs
--  usableRules acc (AF.apply pi -> t) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t@(In in_t):rest)
      | isVar t = go acc rest
      | rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , hIn (icap pi_trs <$> in_t) `unifies` lhs pi_r]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [AF.apply pi . rhs <$> F.toList new, directSubterms t, rest])

iUsableRules_correct trs (Just pi) = F.toList . go mempty where
  pi_trs = AF.apply pi trs
--  usableRules acc (AF.apply pi -> t) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t:rest)
      | isVar t = go acc rest
      | pi_t@(In in_t) <- AF.apply pi t
      , rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , hIn (icap pi_trs <$> in_t) `unifies` lhs pi_r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])
