{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types, KindSignatures #-}

module Narradar.Types.ArgumentFiltering where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Fix (fix)
import Data.Bifunctor
import Data.List (partition, find, inits, unfoldr, sortBy)
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Monoid
import Prelude hiding (lookup, map, and, or)
import qualified Prelude as P

import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Labellings
import Narradar.Types.Term
import Narradar.Framework.Ppr
import Narradar.Utils hiding (fromRight)

import TRSTypes (Mode(..))

import Lattice
import Language.Prolog.SharingAnalysis (SharingAssignment)

#ifdef HOOD
import Debug.Observe
#endif HOOD

extendToTupleSymbols pi = mapSymbols functionSymbol pi `mappend`
                            mapSymbols dpSymbol pi

newtype AF_ id = AF {fromAF:: Map id (Either Int (Set Int))} deriving (Eq, Ord, Show)
type AF = AF_ Id
type LabelledAF = AF_ LId

countPositionsFiltered = sum . fmap length . snd . unzip . toList

init      :: (HasSignature sig) => sig -> AF_ (SignatureId sig)
empty     :: (HasSignature sig) => sig -> AF_ (SignatureId sig)
singleton :: Ord id => id -> [Int] -> AF_ id
singleton':: Ord id => id -> Either Int [Int] -> AF_ id
fromList  :: Ord id => [(id,[Int])] -> AF_ id
fromList' :: Ord id => [(id,Either Int [Int])] -> AF_ id
toList    :: AF_ id -> [(id,[Int])]
toList'   :: AF_ id -> [(id,Either Int [Int])]
lookup    :: (Ord id, Monad m) => id -> AF_ id -> m [Int]
lookup'   :: (Ord id, Monad m) => id -> AF_ id -> m (Either Int [Int])
cut       :: (Pretty id, Ord id) => id -> Int -> AF_ id -> AF_ id
cutAll    :: (Pretty id, Ord id) => [(id, Int)] -> AF_ id -> AF_ id
map       :: (id -> [Int] -> [Int]) -> AF_ id -> AF_ id
map'      :: (id -> Either Int [Int] -> Either Int [Int]) -> AF_ id -> AF_ id
mapSymbols:: Ord id' => (id -> id') -> AF_ id -> AF_ id'
mapSymbols':: Ord id' => (id -> Either Int [Int] -> id') -> AF_ id -> AF_ id'
filter    :: Ord id => (id -> Either Int (Set Int) -> Bool) -> AF_ id -> AF_ id
invert    :: (HasSignature sig) => sig -> AF_ (SignatureId sig) -> AF_ (SignatureId sig)
restrictTo:: Ord id => Set id -> AF_ id -> AF_ id
domain    :: AF_ id -> Set id
splitCD   :: (HasSignature sig, id ~ SignatureId sig, Pretty id) =>  sig -> AF_ id -> (AF_ id, AF_ id)

cut id i (AF m)  = case Map.lookup id m of
                     Nothing -> error ("AF.cut: trying to cut a symbol not present in the AF: " ++ show (pPrint id))
                     Just _ -> AF $ Map.insertWith (flip difference) id (Right $ Set.singleton i) m
cutAll xx af     = Prelude.foldr (uncurry cut) af xx
lookup' id (AF m)= maybe (fail "not found") (return . mapRight Set.toList) (Map.lookup id m)
lookup  id (AF m)= maybe (fail "not found") (return . Set.toList . fromRight) (Map.lookup id m)
fromList         = AF . Map.fromListWith intersection . P.map (second (Right . Set.fromList))
fromList'        = AF . Map.fromListWith intersection . P.map (second (mapRight Set.fromList))
toList (AF af)   = Map.toList (Map.map (Set.toList . fromRight) af)
toList' (AF af)  = Map.toList (Map.map (mapRight Set.toList) af)
singleton  id ii = fromList  [(id,ii)]
singleton' id ii = fromList' [(id,ii)]
map  f (AF af)   = AF$ Map.mapWithKey (\k ii -> Right $ Set.fromList (f k (Set.toList $ fromRight ii))) af
map' f (AF af)   = AF$ Map.mapWithKey (\k ii -> mapRight Set.fromList (f k (mapRight Set.toList ii))) af
filter f (AF af) = AF (Map.filterWithKey f af)
mapSymbols  f (AF af) = AF (Map.mapKeys f af)
mapSymbols' f (AF af) = AF $ Map.fromList [ (f k (mapRight Set.toList v), v) | (k,v) <- Map.toList af ]
invert rules (AF af)
  = AF (Map.mapWithKey
          (\f -> Right . either
                 (\i ->  Set.delete i $ Set.fromDistinctAscList [1..getArity sig f])
                 (\ii -> Set.fromDistinctAscList [1..getArity sig f] `Set.difference` ii))
          af
       )
  where sig = getSignature rules

init t | sig <- getSignature t = fromList
    [ (d, [1 .. a])
          | (d,a) <- Map.toList(getArities sig)
          , a > 0]
empty t | sig <- getSignature t = fromList
    [ (d, []) | d <- F.toList(getDefinedSymbols sig) `mappend`
                     F.toList(getConstructorSymbols sig)]
restrictTo sig (AF af) =
    AF (Map.filterWithKey (\k _ -> k `Set.member` sig) af)
domain (AF pi) = Map.keysSet pi
splitCD sig (AF af) = (af_c, af_d) where
    af_c = AF (Map.filterWithKey (\k _ -> k `Set.member` getConstructorSymbols sig) af)
    af_d = AF (Map.filterWithKey (\k _ -> k `Set.member` getDefinedSymbols     sig) af)


instance Pretty id => Pretty (AF_ id) where
    pPrint af =  fsep $punctuate comma
              [ pPrint f <> colon <+> either (pPrint.id) (pPrint . Set.toList) aa | (f, aa) <-  Map.toList $ fromAF af]

-- | bottom is ill defined
--   It fails the law bottom `join` x = x       (join left identity)
--   However, the law x `join` bottom = x holds (join right identity)
instance Lattice AF where
  meet (AF af1) (AF af2) = AF (Map.unionWith intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith union af1 af2)
  top    = AF mempty
  bottom = AF $ Map.fromList [(AnyIdentifier, Right mempty)]

instance Lattice (AF_ LId) where
  meet (AF af1) (AF af2) = AF (Map.unionWith intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith union af1 af2)
  top    = AF mempty
  bottom = AF $ Map.fromList [(AnyIdentifier, Right mempty)]

instance Ord id => Lattice (AF_ id) where
  meet (AF af1) (AF af2) = AF (Map.unionWith intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith union af1 af2)
  top    = AF mempty


-- | The meet/top monoid
--   There are (at least) two possible monoids, meet/top and join/bottom
--   But only the former makes sense for AFs.
instance Ord id => Monoid (AF_ id) where
  mempty  = AF mempty
  mappend (AF af1) (AF af2) = AF (Map.unionWith intersection af1 af2)

intersection (Right s1) (Right s2) = Right (Set.intersection s1 s2)
intersection (Left x) _ = Left x
intersection _ (Left y) = Left y

union (Right s1) (Right s2) = Right (Set.union s1 s2)
union (Left x)   (Left y)   = Right $ Set.fromList[x,y]
union (Left x)   (Right s2) = Right $ Set.insert x s2
union (Right s1) (Left y)   = Right $ Set.insert y s1

difference (Right s1) (Right s2) = Right (Set.difference s1 s2)
difference (Left x)   (Right s2) = if x `Set.member` s2
                                    then error "AF.difference: cannot further filter a collapsed filtering"
                                    else Left x
difference (Right s1) (Left y)   = Right (Set.delete y s1)
difference (Left x) (Left y)     = if x == y
                                    then error "AF.difference: cannot further filter a collapsed filtering"
                                    else Left x

-- ----------------------
-- Regular AF Application
-- ----------------------
class ApplyAF (t :: *) where
   type AFId t :: *
   apply :: Ord (AFId t) => AF_ (AFId t) -> t -> t

-- type TermN id v = Term (TermF id) v

instance ApplyAF (Term (TermF id) v) where
   type AFId (Term (TermF id) v) = id
   apply = applyTerm

applyTerm :: forall v id . Ord id => AF_ id -> TermN id v -> TermN id v
applyTerm af = foldTerm return f
     where   f t@(Term n tt)
               | Just ii <- lookup' n af = either (\i  -> term n [tt !! pred i])
                                                  (\ii -> term n (select tt (pred <$> ii)))
                                                  ii
               | otherwise = Impure t

instance ApplyAF a => ApplyAF [a] where
    type AFId [a] = AFId a
    apply af = fmap (apply af)

instance (ApplyAF a) => ApplyAF (RuleF a) where
    type AFId (RuleF a) = AFId a
    apply af = fmap (apply af)

instance ApplyAF (Term (WithNote1 n (TermF id)) v) where
    type AFId (Term (WithNote1 n (TermF id)) v) = id
    apply af = foldTerm return f where
      f t@(Note1 (n,Term id tt))
               | Just ii <- lookup' id af = Impure (Note1 (n, Term id (either (\i  -> [tt !! pred i])
                                                                              (\ii -> select tt (pred <$> ii))
                                                                              ii )))
               | otherwise = Impure t

-- -------
-- Sorting
-- -------

sortByDefinedness :: (Ord id, Foldable trs, Size (trs a)) => (AF_ id -> trs a -> trs a) -> trs a -> [AF_ id] -> [AF_ id]
sortByDefinedness apply dps = sortBy (flip compare `on` dpsSize)
    where dpsSize af = size $ (apply af dps)

selectBest = unfoldr findOne where
          findOne [] = Nothing
          findOne (m:xx)
              | any (\x -> Just True == lt m x) xx = findOne xx
              | otherwise = Just (m, P.filter (uncomparableTo m) xx)
              where uncomparableTo x y = isNothing (lt x y)

-- ----------
-- Soundness
-- ----------
isSoundAF :: (ExtraVars v t, Ord (AFId t), ApplyAF t) => AF_ (AFId t) -> t -> Bool
isSoundAF     af trs = null (extraVars $ apply af trs)


-- -----------
-- * Heuristics
-- -----------
-- | The type of heuristics
data Heuristic (id :: *) = Heuristic { runHeu :: forall v t. (Foldable t, HasId t, TermId t ~ id) =>
                                                             AF_ id -> Term t v -> Position -> Set (id, Int)
                                     , isSafeOnDPs :: Bool }

-- | Heuristics with overloading
class PolyHeuristic tag id where runPolyHeu :: tag id -> Heuristic id

-- | Wrapper for heuristics which depend on the problem signature
data MkHeu tag = MkHeu { mkTag :: (HasSignature sig, id ~ SignatureId sig, PolyHeuristic tag id) => sig -> tag id }

-- | Wrapper around a non-overloaded heuristic
data WrapHeu id = WrapHeu ((Ord id) => Heuristic id)
instance (Ord id) => PolyHeuristic WrapHeu id where runPolyHeu (WrapHeu run) = run

simpleHeu ::  (forall id . (Ord id) => Heuristic id) -> MkHeu WrapHeu
simpleHeu h = MkHeu (\_sig -> WrapHeu h)

simpleHeu' ::  (forall id sig. (HasSignature sig, id ~ SignatureId sig ) => sig -> Heuristic id) -> MkHeu WrapHeu
simpleHeu' h = MkHeu (\sig -> WrapHeu (h sig))

mkHeu :: (PolyHeuristic tag id, HasSignature sig, id ~ SignatureId sig) => MkHeu tag -> sig -> Heuristic id
mkHeu (MkHeu mkTag) sig = runPolyHeu (mkTag sig)


bestHeu :: MkHeu WrapHeu
bestHeu = simpleHeu (Heuristic (((Set.fromList .).) . allInner) False)
{-
    predHeuAll  allInner (noConstructors sig ..|..
                         (cond (isDPSymbol.fst) ==> notNullArity ..&.. noUs))
     `or`
-}

innermost, outermost :: forall id . Ord id => Heuristic id
innermost = Heuristic f True where
--   f :: forall v t . (HasId t, Foldable t, TermId t ~ id) => AF_ id -> Term t v -> Position -> Set (id, Int)
   f _ _ [] = mempty
   f _ t pos | Just root <- rootSymbol (t ! Prelude.init pos) = Set.singleton (root, last pos)

outermost = Heuristic f False where
  f _ _ [] = mempty
  f _ t pos | Just root <- rootSymbol t = Set.singleton (root, head pos)

predHeuAll strat pred = f where
  f _  _ []  = mempty
  f af t pos = Set.fromList $ fst $ partition (pred af) (strat af t pos)

predHeuOne strat pred = f where
  f _  _ []  = mempty
  f af t pos = maybe mempty Set.singleton $ find (pred af) (strat af t pos)

allInner _  _ []  = mempty
allInner _ t pos =  [(root, last sub_p)
                                    | sub_p <- reverse (tail $ inits pos)
                                    , Just root <- [rootSymbol (t ! Prelude.init sub_p)]]
allOuter _  _ []  = mempty
allOuter _ t pos =  [(root, last sub_p)
                                    | sub_p <- tail $ inits pos
                                    , Just root <- [rootSymbol (t ! Prelude.init sub_p)]]



typeHeu assig = MkHeu $ \_ -> (TypeHeu assig)

data TypeHeu id = TypeHeu (SharingAssignment String)

instance PolyHeuristic TypeHeu String
   where runPolyHeu (TypeHeu assig) = typeHeu_f assig isUnbounded where
           isUnbounded (p,i) unboundedPositions = (p,i) `Set.member` unboundedPositions

instance (Ord id, Pretty id) => PolyHeuristic TypeHeu id
   where runPolyHeu (TypeHeu assig) = typeHeu_f assig isUnbounded where
           isUnbounded (show.pPrint -> p,i) unboundedPositions = (p,i) `Set.member` unboundedPositions


typeHeu_f :: forall id. Ord id => SharingAssignment String -> ( (id, Int) -> Set (String,Int) -> Bool) -> Heuristic id
typeHeu_f assig isUnbounded = Heuristic (predHeuOne allInner (const f) `or` runHeu innermost) True
  where f (p,i)            = not $ isUnbounded (p,i) unboundedPositions
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


typeHeu2 assig = MkHeu $ \_ -> TypeHeu2 assig

data TypeHeu2 id = TypeHeu2 (SharingAssignment String)

instance PolyHeuristic TypeHeu2 String
   where runPolyHeu (TypeHeu2 assig) = Heuristic (predHeuOne allInner (const f) `or` runHeu innermost) True
             where f (p,i)  = Set.notMember (p,i) reflexivePositions
                   reflexivePositions = Set.fromList [ (f,i) | c <- assig, (f,i) <- F.toList c, i /= 0, (f,0) `Set.member` c]


instance (Ord id, Pretty id) => PolyHeuristic TypeHeu2 id
   where runPolyHeu (TypeHeu2 assig) = Heuristic (predHeuOne allInner (const f) `or` runHeu innermost) True
             where f (show.pPrint -> p,i)  = Set.notMember (p,i) reflexivePositions
                   reflexivePositions = Set.fromList [ (f,i) | c <- assig, (f,i) <- F.toList c, i /= 0, (f,0) `Set.member` c]

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

fromRight (Right x) = x
fromRight _ = error "This AF is collapsing, use primed versions of the functions"

mapRight f = bimap id f
-- ------------
-- debug stuff
-- ------------

#ifdef HOOD
--instance Observable id => Observable (AF_ id) where observer (AF m) = observer m
deriving instance (Pretty id, Observable id) => Observable (AF_ id)
#endif
