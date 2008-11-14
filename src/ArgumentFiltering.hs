{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}

module ArgumentFiltering where

import Control.Arrow (first, second)
import Control.Monad (liftM)
import Data.List ((\\))
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Foldable as Foldable
import Data.Monoid
import Prelude hiding (lookup, map)
import qualified Prelude

import Types
import Utils

newtype AF = AF {fromAF:: Map Identifier (Set Int)} deriving (Eq, Ord, Show)

countPositionsFiltered = sum . fmap length . snd . unzip . toList

empty     :: AF
singleton :: Identifier -> [Int] -> AF
cut       :: Identifier -> [Int] -> AF -> AF
cutAll    :: [(Identifier, [Int])] -> AF -> AF
lookup    :: Monad m => Identifier -> AF -> m [Int]
fromList  :: [(Identifier,[Int])] -> AF


-- | left biased union
union :: AF -> AF -> AF

empty            = AF mempty
singleton id ii  = AF (Map.singleton id (Set.fromList ii))
cut id ii (AF m) = AF $ Map.insertWith (flip Set.difference) id (Set.fromList ii) m
cutAll xx af     = foldr (uncurry cut) af xx
lookup id (AF m) = maybe (fail "not found") (return.Set.toList) (Map.lookup id m)
fromList         = AF . Map.fromListWith Set.union . Prelude.map (second Set.fromList)
toList (AF af)   = Map.toList (Map.map Set.toList af)
null (AF af)     = Map.null af
union (AF m1) (AF m2) = AF$ Map.union m1 m2


map :: (Identifier -> [Int] -> [Int]) -> AF -> AF
map f (AF af) = AF$ Map.mapWithKey (\k ii -> Set.fromList (f k (Set.toList ii))) af

invert :: SignatureC a Identifier => a -> AF -> AF
invert rules (AF af) = AF (Map.mapWithKey (\f ii -> Set.fromDistinctAscList [0..getArity sig f - 1] `Set.difference` ii) af)
  where sig = getSignature rules -- :: Signature (IdFunctions :+*: IdDPs)

class ApplyAF t where applyAF :: AF -> t -> t
instance (Functor f, ApplyAF a) => ApplyAF (f a) where applyAF af = fmap (applyAF af)
instance (TRSC f, T Identifier :<: f) => ApplyAF (Term f) where
    applyAF af = foldTerm f
     where   f t | Just (T (n::Identifier) tt) <- prj t
                 , Just ii       <- lookup n af = term n (select tt ii)
                 | otherwise = inject t

instance ApplyAF (TRS Identifier f) where
    applyAF af trs@TRS{} = tRS$ applyAF af (rules trs)

initAF t | sig <- getSignature t = fromList [ (d, [0.. getArity sig d -1])
                                                 | d <- Foldable.toList(definedSymbols sig `mappend` constructorSymbols sig)]