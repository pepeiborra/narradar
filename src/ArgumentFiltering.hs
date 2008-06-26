{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSignatures, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}

module ArgumentFiltering where

import Control.Arrow (first)
import Data.List ((\\))
import Data.AlaCarte
import qualified Data.Map as Map
import Data.Monoid
import Prelude hiding (lookup, map)

import Types
import Utils

newtype AF = AF {fromAF:: Map.Map Identifier [Int]} deriving (Eq, Ord, Show)

countPositionsFiltered = sum . fmap length . snd . unzip . toList

singleton :: Identifier -> [Int] -> AF
cut    :: Identifier -> [Int] -> AF -> AF
cutAll :: [(Identifier, [Int])] -> AF -> AF
lookup :: Monad m => Identifier -> AF -> m [Int]
fromList :: [(Identifier,[Int])] -> AF
singleton id ii = AF (Map.singleton id ii)
cut id ii (AF map) = AF $ Map.insertWith (flip(\\)) id ii map
cutAll xx af = foldr (uncurry cut) af xx
lookup id (AF map)    = Map.lookup id map
fromList = AF . Map.fromListWith (++)
toList (AF af) = Map.toList af
null (AF af) = Map.null af

map :: (Identifier -> [Int] -> [Int]) -> AF -> AF
map f (AF af) = AF (Map.mapWithKey f af)

invert :: SignatureC a => a -> AF -> AF
invert rules (AF af) = AF (Map.mapWithKey (\f ii -> [0..getArity sig f - 1] \\ ii) af)
  where sig = getSignature rules -- :: Signature (IdFunctions :+*: IdDPs)

class ApplyAF t where applyAF :: AF -> t -> t
instance (Functor f, ApplyAF a) => ApplyAF (f a) where applyAF af = fmap (applyAF af)
instance (TRSC f) => ApplyAF (Term f) where
    applyAF (AF af) = foldTerm f
     where   f t | Just (T (n::Identifier) tt) <- prj t
                 , Just ii       <- Map.lookup n af = term n (select tt ii)
                 | otherwise = inject t

instance ApplyAF (TRS f) where applyAF af trs@TRS{} = tRS$ applyAF af (rules trs)

instance Monoid AF where
  mempty  = AF Map.empty
  mappend (AF m1) (AF m2) = AF$ Map.unionWith (++) m1 m2

initAF t | sig <- getSignature t = fromList [ (d, [0.. getArity sig d -1]) | d <- definedSymbols sig ++ constructorSymbols sig]