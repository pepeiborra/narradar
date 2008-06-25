{-# LANGUAGE PatternSignatures, TypeSynonymInstances, RecordWildCards #-}
module Signature where

import Data.AlaCarte
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

import Types
import {-# SOURCE #-} Problem
import Utils

data Signature = Sig { constructorSymbols :: [Identifier]
                     , definedSymbols :: [Identifier]
                     , arity :: Map Identifier Int}
                 deriving (Show, Eq)

instance Monoid Signature where
    mempty  = Sig mempty mempty mempty
    mappend (Sig c1 s1 a1) (Sig c2 s2 a2) = Sig (mappend c1 c2) (mappend s1 s2) (mappend a1 a2)

class SignatureC a where getSignature :: a -> Signature
instance SignatureC (TRS f) where
  getSignature (TRS rules) =
      Sig{arity= Map.fromList [(f,length tt) | l :-> r <- rules, t <- [l,r]
                                             , Just (T (f::Identifier) tt) <- map match (subterms t)]
         , definedSymbols     = dd
         , constructorSymbols = snub [ root | l :-> r <- rules, t <- subterms r ++ properSubterms l, Just root <- [rootSymbol t]] \\ dd}
    where dd = snub [ root | l :-> _ <- rules, let Just root = rootSymbol l]

instance SignatureC (Problem f) where getSignature (Problem _ (TRS rules) (TRS dps)) = getSignature (TRS $ rules ++ dps)

getArity :: Signature -> Identifier -> Int
getArity Sig{..} f = fromMaybe (error $ "getArity: symbol " ++ show f ++ " not in signature")
                               (Map.lookup f arity)
