{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}

module Narradar.TRS where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.MonadSupply
import Data.Array.IArray
import Data.Graph (Graph)
import Data.Foldable (foldMap, toList)
import Data.List ((\\))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Text.PrettyPrint

import TRS hiding (Ppr, ppr)
import qualified TRS
import Narradar.DPIdentifiers
import Narradar.ProblemType
import Narradar.Utils
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Syntax (Ident)

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
    DPTRS     :: (Ord id, TRSC f, T id :<: f) => Array Int (Rule f) -> Graph -> !(Unifiers f) -> Signature id -> NarradarTRS id f

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

dpTRS typ trs dps edges = dpTRS' typ trs dps' edges
  where dps' = listArray (0, length dps - 1) (refreshRules [0..] dps)

-- | Assumes that the rules have already been renamed apart
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

computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers typ trs dps | (isBNarrowing .|. isGNarrowing) typ
   = array ( (0,0), (length dps -1 , length dps - 1) )
           [((x,y), unify' l (if False then r else head(variant' [r] [l])))
              | (x, _ :-> In in_r) <- zip [0..] dps
              , (y, l :-> _)       <- zip [0..] dps
              , let r = hIn(icap trs <$> in_r) ]

{-
computeDPUnifier typ trs dps (r_i,l_i) | (isBNarrowing .|. isGNarrowing) typ
   =  let (_ :-> In in_r) = dps ! r_i
          (l :-> _)       = dps ! l_i
          r = hIn(icap trs <$> in_r)
      in unify' l (if r_i /= l_i then r else head(variant' [r] [l]))
-}
dpUnify (DPTRS _ _ unifs _) i j = unifs ! (i,j)
--dpUnify (DPTRS _ _ unifs _) i j = unifs !! i !! j

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


-- -----------------
-- Cap & friends
-- -----------------

ren :: (Var :<: f, HashConsed f, Traversable f) => Term f -> Term f
ren t = runSupply (foldTermM f t) where
    f t | Just Var{} <- prj t = var <$> next
        | otherwise           = return (inject t)

cap, icap :: forall trs f id. (Ord id, {-HasTrie (f(Term f)),-} TRSC f, TRS trs id f) => trs -> Term f -> Term f
cap trs t = evalState (go t) freshvv where
  freshvv = map var [0..] \\ vars' t
  go (open -> Just (T (s::id) tt)) | isDefined trs t = next
                                   | otherwise       = term s <$> mapM go tt
  go v = return v

-- Use unification instead of just checking if it is a defined symbol
-- This is not the icap defined in Rene Thiemann. I.e. it does not integrate the REN function
icap trs t = runSupply (go t) where
  go t@(In in_t) | Just (T (f::id) tt) <- open t
                 , f `Set.member` getDefinedSymbols trs = do
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
