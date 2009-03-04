{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE PatternSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}

module Narradar.ArgumentFiltering where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM,liftM2,guard)
import Control.Monad.Fix (fix)
import Data.List ((\\), intersperse, partition, find, inits)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Monoid
import Prelude hiding (lookup, map, and, or)
import qualified Prelude as P

import Narradar.Bottom as Bottom
import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.Convert
import Narradar.Utils

import TRS hiding (apply)
import Lattice
import Language.Prolog.Syntax      (Ident)
import Language.Prolog.TypeChecker (TypeAssignment)

#ifdef DEBUG
import Debug.Trace
#else
trace _ x = x
#endif

extendAFToTupleSymbols pi = pi `mappend` mapSymbols markDPSymbol pi

newtype AF_ id = AF {fromAF:: Map id (Set Int)} deriving (Eq, Ord)
type AF = AF_ Id
type LabelledAF = AF_ LId

instance Show id => Show (AF_ id) where
    show af = -- unlines . fmap show . fmap (second Set.toList) . Map.toList . fromAF
              unlines [ unwords $ intersperse ","
                          [ show f ++ ": " ++ show (Set.toList aa) | (f, aa) <- xx]
                      | xx <- chunks 3 $ Map.toList $ fromAF af]

-- | bottom is ill defined
--   It fails the law bottom `join` x = x       (join left identity)
--   However, the law x `join` bottom = x holds (join right identity)
instance Lattice AF where
  meet (AF af1) (AF af2) = AF (Map.unionWith Set.intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith Set.union af1 af2)
  top    = AF mempty
  bottom = AF $ Map.fromList [(AnyIdentifier, mempty)]

instance Lattice (AF_ LId) where
  meet (AF af1) (AF af2) = AF (Map.unionWith Set.intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith Set.union af1 af2)
  top    = AF mempty
  bottom = AF $ Map.fromList [(AnyIdentifier, mempty)]

instance Ord id => Lattice (AF_ id) where
  meet (AF af1) (AF af2) = AF (Map.unionWith Set.intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith Set.union af1 af2)
  top    = AF mempty


-- | The meet/top monoid
--   There are (at least) two possible monoids, meet/top and join/bottom
--   But only the former makes sense for AFs.
instance Ord id => Monoid (AF_ id) where
  mempty  = AF mempty
  mappend (AF af1) (AF af2) = AF (Map.unionWith Set.intersection af1 af2)

countPositionsFiltered = sum . fmap length . snd . unzip . toList

cut       :: (Show id, Ord id) => id -> Int -> AF_ id -> AF_ id
cutAll    :: (Show id, Ord id) => [(id, Int)] -> AF_ id -> AF_ id
lookup    :: (Ord id, Monad m) => id -> AF_ id -> m [Int]
fromList  :: Ord id => [(id,[Int])] -> AF_ id
toList    :: AF_ id -> [(id,[Int])]
singleton :: Ord id => id -> [Int] -> AF_ id
init      :: (HasSignature sig id, Show id) => sig -> AF_ id
initBottom:: (HasSignature sig id, Show id) => sig -> AF_ id
map       :: (id -> [Int] -> [Int]) -> AF_ id -> AF_ id
mapSymbols:: Ord id' => (id -> id') -> AF_ id -> AF_ id'
mapSymbols':: Ord id' => (id -> [Int] -> id') -> AF_ id -> AF_ id'
filter    :: Ord id => (id -> Set Int -> Bool) -> AF_ id -> AF_ id
invert    :: (Ord id, Show id, TRS a id f) => a -> AF_ id -> AF_ id
restrictTo:: (HasSignature sig id) => sig -> AF_ id -> AF_ id
domain    :: AF_ id -> Set id

cut id i (AF m)  = case Map.lookup id m of
                     Nothing -> error ("AF.cut: trying to cut a symbol not present in the AF: " ++ show id)
                     Just af -> AF $ Map.insertWith (flip Set.difference) id (Set.singleton i) m
cutAll xx af     = Prelude.foldr (uncurry cut) af xx
lookup id (AF m) = maybe (fail "not found") (return.Set.toList) (Map.lookup id m)
fromList         = AF . Map.fromListWith Set.intersection . P.map (second Set.fromList)
toList (AF af)   = Map.toList (Map.map Set.toList af)
singleton id ii  = fromList [(id,ii)]
map f (AF af)    = AF$ Map.mapWithKey (\k ii -> Set.fromList (f k (Set.toList ii))) af
filter f (AF af) = AF (Map.filterWithKey f af)
mapSymbols f (AF af) = AF (Map.mapKeys f af)
mapSymbols' f pi = fromList [ (f k v, v) | (k,v) <- toList pi ]
invert rules (AF af) = AF (Map.mapWithKey (\f ii -> Set.fromDistinctAscList [1..getArity sig f] `Set.difference` ii) af)
  where sig = getSignature rules -- :: Signature (IdFunctions :+*: IdDPs)
init t | sig <- getSignature t = fromList
    [ (d, [1 .. getArity sig d])
          | d <- F.toList(definedSymbols sig `mappend` constructorSymbols sig)
          , getArity sig d > 0]
initBottom t | sig <- getSignature t = fromList
    [ (d, []) | d <- F.toList(definedSymbols sig `mappend` constructorSymbols sig)]
restrictTo (allSymbols.getSignature -> sig) (AF af) =
    AF (Map.filterWithKey (\k _ -> k `Set.member` sig) af)

domain (AF pi) = Map.keysSet pi

--instance Convert (AF_ id) (AF_ id) where convert = id
instance (Convert id id', Ord id') => Convert (AF_ id) (AF_ id') where convert = mapSymbols convert

-- ----------------------
-- Regular AF Application
-- ----------------------
class Ord id => ApplyAF t id | t -> id where apply :: AF_ id -> t -> t

instance (T id :<: f, Ord id) => ApplyAF (Term f) id where
    {-# SPECIALIZE instance ApplyAF (Term BBasicId) Id #-}
    apply = applyTerm

instance (Ord id) => ApplyAF (NarradarTRS id f) id where
    {-# SPECIALIZE instance ApplyAF (NarradarTRS Id BBasicId) Id #-}
    {-# SPECIALIZE instance ApplyAF (NarradarTRS LId BBasicLId) LId #-}
    apply af trs@TRS{} = tRS$ apply af <$$> rules trs
    apply af (PrologTRS cc sig) = PrologTRS (Set.mapMonotonic (\(c,r) ->(c, apply af r)) cc) sig

{-# SPECIALIZE applyTerm :: AF -> Term BBasicId -> Term BBasicId #-}
applyTerm :: forall t id f. (T id :<: f, Ord id) => AF_ id -> Term f -> Term f
applyTerm af = foldTerm f
     where   f t | Just (T (n::id) tt) <- prj t
                 , Just ii       <- lookup n af = term n (select tt (pred <$> ii))
                 | otherwise = inject t

instance ApplyAF a id => ApplyAF [a] id where apply af = fmap (apply af)
instance (T id :<: f, Ord id) => ApplyAF (Rule f) id where apply af = fmap (apply af)

-- --------------------------
-- Custom rhs AF Application
-- --------------------------
class Ord id => ApplyAF_rhs t sig id | t -> id where apply_rhs :: sig -> AF_ id -> t -> t

instance (T id :<: f, Ord id) => ApplyAF_rhs (Term f) sig id where
    {-# off SPECIALIZE instance ApplyAF_rhs (Term BBasicId) (Problem BBasicId) Id #-}
    apply_rhs _ = applyTerm

instance (Bottom :<: f, Ord id) => ApplyAF_rhs (NarradarTRS id f) sig id where
    {-# SPECIALIZE instance ApplyAF_rhs (NarradarTRS Id  BBasicId)  (NarradarTRS Id  BBasicId)  Id #-}
    {-# SPECIALIZE instance ApplyAF_rhs (NarradarTRS LId BBasicLId) (NarradarTRS LId BBasicLId) LId #-}
    apply_rhs _ af trs@TRS{} = tRS$ applyToRule (getSignature trs) af <$> rules trs
    apply_rhs _ af (PrologTRS cc sig) = PrologTRS (Set.mapMonotonic (\(c,r) ->(c, applyToRule sig af r)) cc) sig

instance (Bottom :<: f, Var :<: f, T id :<: f, Ord id, HasSignature sig id) => ApplyAF_rhs (Rule f) sig id where
    apply_rhs sig = applyToRule (getSignature sig)

instance ApplyAF_rhs a sig id => ApplyAF_rhs [a] sig id where apply_rhs sig af = fmap (apply_rhs sig af)

{-# SPECIALIZE applyToRule :: Signature Id -> AF -> Rule BBasicId -> Rule BBasicId #-}
applyToRule :: (Bottom :<: f, Var :<: f, Ord id, T id :<: f) => Signature id -> AF_ id -> Rule f -> Rule f
applyToRule sig af (lhs :-> rhs) = apply af lhs :-> applyToRhs af rhs
  where
    -- applyToRhs cuts vars to bottoms
    applyToRhs _ (open -> Just Var{}) = Bottom.bottom
    applyToRhs af t@(open -> Just (T n tt))
      | n `Set.member` constructorSymbols sig
      = case lookup n af of
          Just ii -> term n (applyToRhs af <$> select tt (pred <$> ii))
          Nothing -> term n (applyToRhs af <$> tt)
    applyToRhs af t = apply af t  -- we don't cut vars below defined symbols


-- -----------
-- Heuristics
-- -----------
type Heuristic id f = AF_ id -> Term f -> Position -> Set (id, Int)
convertHeu heu af t p = heu (convert af) (convert t) p

--bestHeu, innermost, outermost, noConstructors, noUs, allPos :: sig -> Heuristic id f

{-# noSPECIALIZE bestHeu :: NarradarTRS Id BBasicId -> AF -> Term BBasicId -> Position -> Set (Id,Int) #-}

bestHeu :: (Foldable f, T id :<: f, HasSignature sig id) => sig -> Heuristic id f
bestHeu (getSignature -> sig) =
{-
    predHeuAll  allInner (noConstructors sig ..|..
                         (cond (isDPSymbol.fst) ==> notNullArity ..&.. noUs))
     `or`
-}
    (((Set.fromList .).) . allInner)

innermost _ _ [] = mempty
innermost af t pos | Just root <- rootSymbol (t ! Prelude.init pos) = Set.singleton (root, last pos)
outermost _ _ [] = mempty
outermost af t pos | Just root <- rootSymbol t = Set.singleton (root, head pos)

predHeuAll _     _    _  _ []  = mempty
predHeuAll strat pred af t pos = Set.fromList $ fst $ partition (pred af) (strat af t pos)

predHeuOne _     _    _  _ []  = mempty
predHeuOne strat pred af t pos = maybe mempty Set.singleton $ find (pred af) (strat af t pos)

allInner _  _ []  = mempty
allInner af t pos =  [(root, last sub_p)
                                    | sub_p <- reverse (tail $ inits pos)
                                    , Just root <- [rootSymbol (t ! Prelude.init sub_p)]]

--typeHeu :: Foldable f => Signature Ident -> TypeAssignment -> Heuristic id f
typeHeu assig =
    predHeuOne allInner (const f) `or` innermost
  where f (show -> p,i)  = Set.notMember (p,i) unboundedPositions
        constructorSymbols = Set.fromList [f | c <- assig, (f,0) <- F.toList c]
        unboundedPositions = fix unboundedF reflexivePositions
        unboundedF f uu | trace ("unboundedF: " ++ show uu) False = undefined
        unboundedF f uu | null new = uu
                        | otherwise= f(Set.fromList new `mappend` uu)
           where new =  [ p | c <- assig
                            , p <- F.toList c
                            , p `Set.notMember` uu
                            , (g,0) <- F.toList (Set.delete p c)
                            , any (`Set.member` uu) (zip (repeat g) [1..getArity g])]
        reflexivePositions = Set.fromList [ (f,i) | c <- assig, (f,i) <- F.toList c, i /= 0, (f,0) `Set.member` c]
        getArity g | Just i <- Map.lookup g arities = i
        arities = Map.fromListWith max (concatMap F.toList assig) :: Map Ident Int

-- Ignore unbounded positions
typeHeu2 assig =
    predHeuOne allInner (\ _ (p,i) -> -- not(isDPSymbol p)) &&
                                         ((Set.notMember (p) constructorSymbols)
                                        ||
                                          (Set.notMember (p,i) reflexivePositions)))
   `or` innermost
  where constructorSymbols = Set.fromList [f | c <- assig, (f,0) <- F.toList c]
        unboundedPositions = fix unboundedF reflexivePositions
        unboundedF f uu | trace ("unboundedF: " ++ show uu) False = undefined
        unboundedF f uu | null new = uu
                        | otherwise= f(Set.fromList new `mappend` uu)
           where new =  [ p | c <- assig
                            , p <- F.toList c
                            , p `Set.notMember` uu
                            , (g,0) <- F.toList (Set.delete p c)
                            , any (`Set.member` uu) (zip (repeat g) [1..getArity g])]
        reflexivePositions = Set.fromList [ (f,i) | c <- assig, (f,i) <- F.toList c, i /= 0, (f,0) `Set.member` c]
        getArity g | Just i <- Map.lookup g arities = i
        arities = Map.fromListWith max (concatMap F.toList assig) :: Map Ident Int

-- Predicates
-- ----------
noConstructors sig _pi (f,_) = f `Set.notMember` constructorSymbols sig

noUs _ (UId _) = False
noUs _ _ = True

notNullArity af (s,_) | Just [_] <- lookup s af = False
                      | otherwise               = True

-- Combinators
-- -----------
and h1 h2 af t pos = let
    afs1 = h1 af t pos
    afs2 = h2 af t pos
    in afs1 `Set.intersection` afs2

or h1 h2 af t pos =  case h1 af t pos of
                        afs | Set.null afs -> h2 af t pos
                            | otherwise    -> afs

cond f _ x = f x

f ==> g = ((not.). f) ..|.. g
infixr 2 ==>