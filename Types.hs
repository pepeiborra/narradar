{-# LANGUAGE TemplateHaskell, UndecidableInstances, OverlappingInstances, RecordWildCards #-}
module Types (module TRS, module Types) where

import Control.Monad
import Data.AlaCarte
import Data.Foldable
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import TRS
import qualified TRS

import Prelude as P
import Utils

newtype TRS sig a = TRS [Rule a] deriving (Show)
type IdFunctions = String
newtype IdDPs = IdDP String deriving (Eq, Ord)

instance Show IdDPs where show (IdDP n) = n ++ "#"

type DP a = Rule a

type T = TRS.IdFunctions

markSymbol = IdDP
unmarkSymbol (IdDP n) = n

markDP, unmarkDP :: (T IdFunctions :<: f, T IdDPs :<: f) => Term f -> Term f
markDP t | Just (T (n::IdFunctions) tt) <- match t = term (IdDP n) tt
         | otherwise                = t
unmarkDP t | Just (T (IdDP n) tt) <- match t = term n tt
           | otherwise                       = t

data Identifiers = IdFunction IdFunctions | IdDP' IdDPs
  deriving (Eq, Ord, Show)

class    Identifier a           where wrap :: a -> Identifiers
instance Identifier IdFunctions where wrap = IdFunction
instance Identifier IdDPs       where wrap = IdDP'
instance Identifier Identifiers where wrap = id

isGround :: (Var :<: f, Foldable f) => Term f -> Bool
isGround = null . vars

hasExtraVars :: (Var :<: f, Foldable f) => TRS sig f -> Bool
hasExtraVars (TRS trs) = not $ P.all null [vars r \\ vars l | l :-> r <- trs]

newtype Signature a = Sig {arity :: Map Identifiers Int}

instance Monoid (Signature a) where
    mempty  = Sig mempty
    mappend (Sig s1) (Sig s2) = Sig $ mappend s1 s2

appendSig :: Signature a -> Signature b -> Signature (a :+*: b)
appendSig (Sig a) (Sig b) = Sig (Map.union a b)

matchT :: forall sig f. MatchTerm sig f => TRS sig f -> Term f -> Maybe (T Identifiers (Term f))
matchT _ = matchTerm (proxy::sig)

class MatchTerm sig f where matchTerm :: sig -> Term f -> Maybe (T Identifiers (Term f))
instance (T IdFunctions :<: f) => MatchTerm IdFunctions f where matchTerm _ t = match t >>= \ (T (f::IdFunctions) tt) -> Just $ T (wrap f) tt
instance (T IdDPs :<: f) => MatchTerm IdDPs f where matchTerm _ t = match t >>= \(T (f::IdDPs) tt) -> Just (T (wrap f) tt)
instance   (MatchTerm a f, MatchTerm b f) => MatchTerm (a :+*: b) f where
    matchTerm sig t = matchTerm (proxy::a) t `mplus` matchTerm (proxy::b) t

getSignature :: forall sig f. (MatchTerm sig f, Functor f, Foldable f) => TRS sig f -> Signature sig
getSignature trs@(TRS rules) =
      Sig{arity= Map.fromList [(f,length tt) | l :-> r <- rules, t <- [l,r]
                                             , Just (T f tt) <- map (matchT trs) (subterms t)]}

getArity :: (Identifier a, a :<*: b) => Signature b -> a -> Int
getArity Sig{..} f = fromMaybe (error "getArity: symbol not in signature")
                               (Map.lookup (wrap f) arity)

data a :+*: b = a :+*: b
class (:<*:) sub sup
instance (:<*:) a a
instance (:<*:) a (a :+*: b)
instance (b :<*: c) => (:<*:) b (a :+*: c)

proxy :: a
proxy = undefined

sig :: TRS sig f -> sig
sig _ = undefined

l (l :+*: _) = l
r (_ :+*: r) = r