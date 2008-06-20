{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
module ArgumentFiltering where

import Control.Arrow (first)
import Data.List ((\\))
import Data.AlaCarte
import Data.Foldable
import qualified Data.Map as Map
import Data.Monoid
import Types
import Utils
import Prelude hiding (lookup, map)

newtype AF sig = AF {fromAF:: Map.Map Identifiers [Int]} deriving (Eq, Ord, Show)

singleton :: Identifier a => a -> [Int] -> AF a
insert :: Identifier a => a -> [Int] -> AF -> AF a
lookup :: (Identifier a, Monad m) => a -> AF -> m [Int]
fromList :: Identifier a => [(a,[Int])] -> AF a
singleton id ii = AF (Map.singleton (wrap id) ii)
insert id ii (AF map) = AF $ Map.insertWith (++) (wrap id) ii map
lookup id (AF map)    = Map.lookup (wrap id) map
fromList = AF . Map.fromListWith (++) . fmap (first wrap)
toList (AF af) = Map.toList af
null (AF af) = Map.null af

map :: (Identifiers -> [Int] -> [Int]) -> AF sig -> AF sig
map f (AF af) = AF (Map.mapWithKey f af)

--invert :: (T IdFunctions :<: f, T IdDPs :<: f, Foldable f) => TRS f -> AF -> AF
invert rules (AF af) = AF (Map.mapWithKey (\f ii -> [0..getArity sig f - 1] \\ ii) af)
  where sig = getSignature rules -- :: Signature (IdFunctions :+*: IdDPs)

class ApplyAF t sig where applyAF :: AF sig -> t -> t
instance (Functor f, ApplyAF a sig) => ApplyAF (f a) sig where applyAF af = fmap (applyAF af)
instance (Identifier a, T a :<: f, Identifier b, T b :<: b, Functor f) => ApplyAF (Term f) (a :+: b) where
    applyAF (AF af) = foldTerm f
     where   f t | Just (T n tt) <- matchT (proxy::Sig) (In t)
                 , Just ii       <- Map.lookup n af = term (unwrap n) (select tt ii)
                 | otherwise = inject t

--instance ApplyAF (TRS sig a) where applyAF af (TRS rules) = TRS $ applyAF af rules

instance Monoid AF where
  mempty  = AF Map.empty
  mappend (AF m1) (AF m2) = AF$ Map.unionWith (++) m1 m2