{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}

module ArgumentFiltering where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM)
import Data.List ((\\), intersperse)
import Data.Map (Map)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as Foldable
import Data.Monoid
import Prelude hiding (lookup, map)
import qualified Prelude

import {-# SOURCE #-} Types
import TRS hiding (apply)
import Utils
import Lattice

newtype AF = AF {fromAF:: Map Identifier (Set Int)} deriving (Eq, Ord)

instance Show AF where show af = -- unlines . fmap show . fmap (second Set.toList) . Map.toList . fromAF
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

-- | The meet/top monoid
--   There are (at least) two possible monoids, meet/top and join/bottom
--   But only the former makes sense for AFs.
instance Monoid AF where
  mempty  = top
  mappend = meet

countPositionsFiltered = sum . fmap length . snd . unzip . toList

cut       :: Identifier -> Int -> AF -> AF
cutAll    :: [(Identifier, Int)] -> AF -> AF
lookup    :: Monad m => Identifier -> AF -> m [Int]
fromList  :: [(Identifier,[Int])] -> AF

cut id i (AF m) = AF $ Map.insertWith (flip Set.difference) id (Set.singleton i) m
cutAll xx af     = foldr (uncurry cut) af xx
lookup id (AF m) = maybe (fail "not found") (return.Set.toList) (Map.lookup id m)
fromList         = AF . Map.fromListWith Set.union . Prelude.map (second Set.fromList)
toList (AF af)   = Map.toList (Map.map Set.toList af)

map :: (Identifier -> [Int] -> [Int]) -> AF -> AF
map f (AF af) = AF$ Map.mapWithKey (\k ii -> Set.fromList (f k (Set.toList ii))) af

invert :: SignatureC a Identifier => a -> AF -> AF
invert rules (AF af) = AF (Map.mapWithKey (\f ii -> Set.fromDistinctAscList [1..getArity sig f] `Set.difference` ii) af)
  where sig = getSignature rules -- :: Signature (IdFunctions :+*: IdDPs)

class ApplyAF t where apply :: AF -> t -> t
instance (TRSC f, T Identifier :<: f) => ApplyAF (Term f) where
    apply af = foldTerm f
     where   f t | Just (T (n::Identifier) tt) <- prj t
                 , Just ii       <- lookup n af = term n (select tt (pred <$> ii))
                 | otherwise = inject t

instance ApplyAF (TRS Identifier f) where apply af trs@TRS{} = tRS'$ apply af (rules trs)

--instance (Functor f, ApplyAF a) => ApplyAF (f a) where apply af = fmap (apply af)
-- The Functor instance can lead to subtle bugs. Replaced with individual instances
instance ApplyAF a => ApplyAF [a]                            where apply af = fmap (apply af)
instance (TRSC f, T Identifier :<: f) => ApplyAF (Rule f)    where apply af = fmap (apply af)
instance (TRSC f, T Identifier :<: f) => ApplyAF (Problem f) where apply af = fmap (apply af)

init t | sig <- getSignature t = fromList
    [ (d, [1 .. getArity sig d])
          | d <- Foldable.toList(definedSymbols sig `mappend` constructorSymbols sig)
          , getArity sig d > 0]