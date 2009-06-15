{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types, KindSignatures #-}

module Narradar.ArgumentFiltering where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM,liftM2,guard)
import Control.Monad.Fix (fix)
import qualified Data.Array.IArray as A
import Data.List ((\\), intersperse, partition, find, inits)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Monoid
import Data.Term hiding (find)
import Data.Term.Rules
import Data.Term.Ppr
import Data.Traversable (Traversable,sequenceA)
import Text.PrettyPrint
import Prelude hiding (lookup, map, and, or)
import qualified Prelude as P

import Narradar.DPIdentifiers
import Narradar.PrologIdentifiers
import Narradar.Labellings
import Narradar.Utils
import Narradar.Term

import TRSTypes (Mode(..))

import Lattice
import Language.Prolog.SharingAnalysis (SharingAssignment)

#ifdef HOOD
import Debug.Observe
#endif HOOD

mkGoalAF (f, tt) = singleton f [ i | (i,G) <- zip [1..] tt]

extendToTupleSymbols pi = mapSymbols functionSymbol pi `mappend`
                            mapSymbols dpSymbol pi

newtype AF_ id = AF {fromAF:: Map id (Set Int)} deriving (Eq, Ord, Show)
type AF = AF_ Id
type LabelledAF = AF_ LId

instance Ppr id => Ppr (AF_ id) where
    ppr af =  vcat [ hcat $ punctuate comma
                          [ ppr f <> colon <+> ppr (Set.toList aa) | (f, aa) <- xx]
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

init      :: (HasSignature sig id, Ord id, Ppr id) => sig -> AF_ id
empty     :: (HasSignature sig id,  Ord id, Ppr id) => sig -> AF_ id
singleton :: Ord id => id -> [Int] -> AF_ id
fromList  :: Ord id => [(id,[Int])] -> AF_ id
toList    :: AF_ id -> [(id,[Int])]
lookup    :: (Ord id, Monad m) => id -> AF_ id -> m [Int]
cut       :: (Ppr id, Ord id) => id -> Int -> AF_ id -> AF_ id
cutAll    :: (Ppr id, Ord id) => [(id, Int)] -> AF_ id -> AF_ id
map       :: (id -> [Int] -> [Int]) -> AF_ id -> AF_ id
mapSymbols:: Ord id' => (id -> id') -> AF_ id -> AF_ id'
mapSymbols':: Ord id' => (id -> [Int] -> id') -> AF_ id -> AF_ id'
filter    :: Ord id => (id -> Set Int -> Bool) -> AF_ id -> AF_ id
invert    :: (Ord id, Ppr id, HasSignature sig id) => sig -> AF_ id -> AF_ id
restrictTo:: Ord id => Set id -> AF_ id -> AF_ id
domain    :: AF_ id -> Set id
splitCD   :: (HasSignature sig id, Ord id, Ppr id) =>  sig -> AF_ id -> (AF_ id, AF_ id)

cut id i (AF m)  = case Map.lookup id m of
                     Nothing -> error ("AF.cut: trying to cut a symbol not present in the AF: " ++ show (ppr id))
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
  where sig = getSignature rules
init t | sig <- getSignature t = fromList
    [ (d, [1 .. getArity sig d])
          | d <- F.toList(definedSymbols sig `mappend` constructorSymbols sig)
          , getArity sig d > 0]
empty t | sig <- getSignature t = fromList
    [ (d, []) | d <- F.toList(definedSymbols sig `mappend` constructorSymbols sig)]
restrictTo sig (AF af) =
    AF (Map.filterWithKey (\k _ -> k `Set.member` sig) af)
domain (AF pi) = Map.keysSet pi
splitCD sig (AF af) = (af_c, af_d) where
    af_c = AF (Map.filterWithKey (\k _ -> k `Set.member` getConstructorSymbols sig) af)
    af_d = AF (Map.filterWithKey (\k _ -> k `Set.member` getDefinedSymbols     sig) af)

-- ----------------------
-- Regular AF Application
-- ----------------------
class    Ord id => ApplyAF t id | t ->  id where apply :: AF_ id -> t -> t
instance Ord id => ApplyAF (TermN id v) id where apply = applyTerm

applyTerm :: forall v id . Ord id => AF_ id -> TermN id v -> TermN id v
applyTerm af = foldTerm return f
     where   f t@(Term n tt)
               | Just ii <- lookup n af = term n (select tt (pred <$> ii))
               | otherwise = Impure t

instance ApplyAF a id => ApplyAF [a] id where apply af = fmap (apply af)
instance (Ord id, ApplyAF a id) => ApplyAF (RuleF a) id where apply af = fmap (apply af)
instance (Functor f, ApplyAF t id) => ApplyAF (f t) id  where apply af = fmap (apply af)

instance (Ord id) => ApplyAF (Free (WithNote1 n (TermF id)) v) id  where
    apply af = foldTerm return f where
      f t@(Note1 (n,Term id tt))
               | Just ii <- lookup id af = Impure (Note1 (n, Term id (select tt (pred <$> ii))))
               | otherwise = Impure t

-- -----------
-- * Heuristics
-- -----------
-- | The type of heuristics
data Heuristic id t = Heuristic { runHeu :: forall v. AF_ id -> Term t v -> Position -> Set (id, Int), isSafeOnDPs::Bool }
type HeuristicN id = Heuristic id (TermF id)

-- | Heuristics with overloading
class PolyHeuristic tag id f where runPolyHeu :: tag id f -> Heuristic id f
class PolyHeuristic tag id (TermF id) => PolyHeuristicN tag id; instance PolyHeuristic tag id (TermF id) => PolyHeuristicN tag id

-- | Wrapper for heuristics which depend on the problem signature
data MkHeu tag = MkHeu { mkTag :: (HasSignature sig id, PolyHeuristic tag id f) => sig -> tag id f }

-- | Wrapper around a non-overloaded heuristic
data WrapHeu id f = WrapHeu ((Foldable f, HasId f id, Ord id, Ppr id) => Heuristic id f)
instance (Ord id, Ppr id, HasId f id, Foldable f) => PolyHeuristic WrapHeu id f where runPolyHeu (WrapHeu run) = run

simpleHeu ::  (forall id f. (Foldable f, HasId f id, Ord id, Ppr id) => Heuristic id f) -> MkHeu WrapHeu
simpleHeu h = MkHeu (\sig -> WrapHeu h)

simpleHeu' ::  (forall id f sig. (Foldable f, Ord id, Ppr id, HasSignature sig id) => sig -> Heuristic id f) -> MkHeu WrapHeu
simpleHeu' h = MkHeu (\sig -> WrapHeu (h sig))

mkHeu :: (PolyHeuristic tag id f, HasSignature sig id) => MkHeu tag -> sig -> Heuristic id f
mkHeu (MkHeu mkTag) sig = runPolyHeu (mkTag sig)


bestHeu :: MkHeu WrapHeu
bestHeu = simpleHeu (Heuristic (((Set.fromList .).) . allInner) False)
{-
    predHeuAll  allInner (noConstructors sig ..|..
                         (cond (isDPSymbol.fst) ==> notNullArity ..&.. noUs))
     `or`
-}

innermost = Heuristic f True where
   f _ _ [] = mempty
   f af t pos | Just root <- rootSymbol (t ! Prelude.init pos) = Set.singleton (root, last pos)

outermost = Heuristic f False where
  f _ _ [] = mempty
  f af t pos | Just root <- rootSymbol t = Set.singleton (root, head pos)

predHeuAll strat pred = f where
  f _  _ []  = mempty
  f af t pos = Set.fromList $ fst $ partition (pred af) (strat af t pos)

predHeuOne strat pred = f where
  f _  _ []  = mempty
  f af t pos = maybe mempty Set.singleton $ find (pred af) (strat af t pos)

allInner _  _ []  = mempty
allInner af t pos =  [(root, last sub_p)
                                    | sub_p <- reverse (tail $ inits pos)
                                    , Just root <- [rootSymbol (t ! Prelude.init sub_p)]]
allOuter _  _ []  = mempty
allOuter af t pos =  [(root, last sub_p)
                                    | sub_p <- tail $ inits pos
                                    , Just root <- [rootSymbol (t ! Prelude.init sub_p)]]

typeHeu assig = MkHeu $ \_ -> (TypeHeu assig)

data TypeHeu id (f :: * -> *) = TypeHeu (SharingAssignment String)

instance (HasId f String, Foldable f) => PolyHeuristic TypeHeu String f
   where runPolyHeu (TypeHeu assig) = typeHeu_f assig isUnbounded where
           isUnbounded (p,i) unboundedPositions = (p,i) `Set.member` unboundedPositions

instance (HasId f id, Ppr id, Ord id, Foldable f) => PolyHeuristic TypeHeu id f
   where runPolyHeu (TypeHeu assig) = typeHeu_f assig isUnbounded where
           isUnbounded (show.ppr -> p,i) unboundedPositions = (p,i) `Set.member` unboundedPositions

typeHeu_f assig isUnbounded = Heuristic (predHeuOne allInner (const f) `or` runHeu innermost) True
  where f (p,i)            = not $ isUnbounded (p,i) unboundedPositions
        constructorSymbols = Set.fromList [f | c <- assig, (f,0) <- F.toList c]
        unboundedPositions = fix unboundedF reflexivePositions
--        unboundedF f uu | trace ("unboundedF: " ++ show uu) False = undefined
        unboundedF f uu | null new = uu
                        | otherwise= f(Set.fromList new `mappend` uu)
           where new =  [ p | c <- assig
                            , p <- F.toList c
                            , p `Set.notMember` uu
                            , (g,0) <- F.toList (Set.delete p c)
                            , any (`Set.member` uu) (zip (repeat g) [1..getArity g])]
        reflexivePositions = Set.fromList [ (f,i) | c <- assig, (f,i) <- F.toList c, i /= 0, (f,0) `Set.member` c]
        getArity g | Just i <- Map.lookup g arities = i
        arities = Map.fromListWith max (concatMap F.toList assig) -- :: Map Ident Int

--typeHeu :: Foldable f => Signature Ident -> TypeAssignment -> Heuristic id f
typeHeu2 assig = simpleHeu $ Heuristic (predHeuOne allInner (const f) `or` runHeu innermost) True
  where f (show.ppr -> p,i)  = Set.notMember (p,i) reflexivePositions
        constructorSymbols = Set.fromList [f | c <- assig, (f,0) <- F.toList c]
        unboundedPositions = fix unboundedF reflexivePositions
--        unboundedF f uu | trace ("unboundedF: " ++ show uu) False = undefined
        unboundedF f uu | null new = uu
                        | otherwise= f(Set.fromList new `mappend` uu)
           where new =  [ p | c <- assig
                            , p <- F.toList c
                            , p `Set.notMember` uu
                            , (g,0) <- F.toList (Set.delete p c)
                            , any (`Set.member` uu) (zip (repeat g) [1..getArity g])]
        reflexivePositions = Set.fromList [ (f,i) | c <- assig, (f,i) <- F.toList c, i /= 0, (f,0) `Set.member` c]
        getArity g | Just i <- Map.lookup g arities = i
        arities = Map.fromListWith max (concatMap F.toList assig) -- :: Map Ident Int

-- Predicates
-- ----------
noConstructors sig _pi (f,_) = f `Set.notMember` getConstructorSymbols sig

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

-- ------------
-- debug stuff
-- ------------

#ifdef HOOD
--instance Observable id => Observable (AF_ id) where observer (AF m) = observer m
deriving instance (Ppr id, Observable id) => Observable (AF_ id)
#endif
