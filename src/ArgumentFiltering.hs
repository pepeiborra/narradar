{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module ArgumentFiltering where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM,liftM2,guard)
import Data.List ((\\), intersperse, inits)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as Foldable
import Data.Foldable (Foldable)
import Data.Monoid
import Prelude hiding (lookup, map, and, or)
import qualified Prelude

import Bottom
import Identifiers
import TRS hiding (apply)
import Utils
import Lattice

newtype AF_ id = AF {fromAF:: Map id (Set Int)} deriving (Eq, Ord)
type AF = AF_ Identifier
type LabelledAF = AF_ (Labelled Identifier)

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

instance Lattice (AF_ (Labelled Identifier)) where
  meet (AF af1) (AF af2) = AF (Map.unionWith Set.intersection af1 af2)
  join (AF af1) (AF af2) = AF (Map.unionWith Set.union af1 af2)
  top    = AF mempty
  bottom = AF $ Map.fromList [(Plain AnyIdentifier, mempty)]

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
singleton :: Ord id => id -> [Int] -> AF_ id
init      :: (SignatureC sig id, Show id) => sig -> AF_ id

cut id i (AF m)  = case Map.lookup id m of
                     Nothing -> error ("AF.cut: trying to cut a symbol not present in the AF: " ++ show id)
                     Just af -> AF $ Map.insertWith (flip Set.difference) id (Set.singleton i) m
cutAll xx af     = Prelude.foldr (uncurry cut) af xx
lookup id (AF m) = maybe (fail "not found") (return.Set.toList) (Map.lookup id m)
fromList         = AF . Map.fromListWith Set.intersection . Prelude.map (second Set.fromList)
toList (AF af)   = Map.toList (Map.map Set.toList af)
singleton id ii  = fromList [(id,ii)]
map :: (id -> [Int] -> [Int]) -> AF_ id -> AF_ id
map f (AF af) = AF$ Map.mapWithKey (\k ii -> Set.fromList (f k (Set.toList ii))) af

mapKeys f (AF af) = AF (Map.mapKeys f af)

invert :: (Ord id, Show id, TRS a id f) => a -> AF_ id -> AF_ id
invert rules (AF af) = AF (Map.mapWithKey (\f ii -> Set.fromDistinctAscList [1..getArity sig f] `Set.difference` ii) af)
  where sig = getSignature rules -- :: Signature (IdFunctions :+*: IdDPs)

--init :: (SignatureC sig id) => sig -> AF_ id
init t | sig <- getSignature t = fromList
    [ (d, [1 .. getArity sig d])
          | d <- Foldable.toList(definedSymbols sig `mappend` constructorSymbols sig)
          , getArity sig d > 0]

--instance Convert (AF_ id) (AF_ id) where convert = id
instance (Convert id id', Ord id') => Convert (AF_ id) (AF_ id') where convert = mapKeys convert

-- ----------------------
-- Regular AF Application
-- ----------------------
class Ord id => ApplyAF t id | t -> id where apply :: AF_ id -> t -> t

instance (T id :<: f, Ord id) => ApplyAF (Term f) id where
    {-# SPECIALIZE instance ApplyAF (Term BBasicId) Id #-}
    apply = applyTerm

instance (Bottom :<: f, Ord id) => ApplyAF (NarradarTRS id f) id where
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

instance (Bottom :<: f, Var :<: f, T id :<: f, Ord id, SignatureC sig id) => ApplyAF_rhs (Rule f) sig id where
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
--bestHeu, innermost, outermost, noConstructors, noUs, allPos :: sig -> Heuristic id f

{-# noSPECIALIZE bestHeu :: NarradarTRS Id BBasicId -> AF -> Term BBasicId -> Position -> Set (Id,Int) #-}

bestHeu :: (Foldable f, DPSymbol id, T id :<: f, SignatureC sig id) => sig -> Heuristic id f
bestHeu = predHeu allInner (noConstructors ...|... cond isDP ===> notNullArity ...&... noUs ) `or` allInner

innermost _ _ _ [] = mempty
innermost p af t pos | Just root <- rootSymbol (t ! Prelude.init pos) = Set.singleton (root, last pos)
outermost _ _ _ [] = mempty
outermost p af t pos | Just root <- rootSymbol t = Set.singleton (root, head pos)

predHeu _     _    _ _  _ []  = mempty
predHeu strat pred p af t pos = fst $ Set.partition (pred p af . fst) (strat p af t pos)

allInner _ _  _ []  = mempty
allInner _ af t pos = Set.fromList [(root, last sub_p)
                                    | sub_p <- reverse (tail $ inits pos)
                                    , Just root <- [rootSymbol (t ! Prelude.init sub_p)]]

-- Predicates
-- ----------
noConstructors p _ = not . (`Set.member` constructorSymbols (getSignature p))

noUs _ _ (symbol -> ('u':'_':_)) = False
noUs _ _ _ = True

noDPs _ _ = not . isDP

noUsDPs _ _ s@(symbol -> ('u':'_':_)) = not(isDP s)
noUsDPs _ _ _ = True

notNullArity _ af s | Just [_] <- lookup s af = False
                    | otherwise               = True

and h1 h2 p af t pos = let
    afs1 = h1 p af t pos
    afs2 = h2 p af t pos
    in afs1 `Set.intersection` afs2

or h1 h2 p af t pos =  case h1 p af t pos of
                        afs | Set.null afs -> h2 p af t pos
                            | otherwise    -> afs

(...&...) = (liftM2.liftM2.liftM2) (&&) --(f &...& g) x y z = f x y z && g x y
(...|...) = (liftM2.liftM2.liftM2) (||)
f ===> g = (((not.).). f) ...|... g
cond f _ _ x = f x

infixr 3 ...&...
infixr 3 ...|...
infixr 2 ===>