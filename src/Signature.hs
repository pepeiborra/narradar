{-# LANGUAGE PatternSignatures, TypeSynonymInstances, RecordWildCards #-}
module Signature where

import Data.AlaCarte
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

import Types
import {-# SOURCE #-} Problem

newtype Signature = Sig {arity :: Map Identifier Int}

instance Monoid Signature where
    mempty  = Sig mempty
    mappend (Sig s1) (Sig s2) = Sig $ mappend s1 s2

appendSig :: Signature -> Signature -> Signature
appendSig (Sig a) (Sig b) = Sig (Map.union a b)

class SignatureC a where getSignature :: a -> Signature
instance SignatureC (TRS f) where
  getSignature (TRS rules) =
      Sig{arity= Map.fromList [(f,length tt) | l :-> r <- rules, t <- [l,r]
                                             , Just (T (f::Identifier) tt) <- map match (subterms t)]}
instance SignatureC (Problem f) where getSignature (Problem _ (TRS rules) (TRS dps)) = getSignature (TRS $ rules ++ dps)

getArity :: Signature -> Identifier -> Int
getArity Sig{..} f = fromMaybe (error $ "getArity: symbol " ++ show f ++ " not in signature")
                               (Map.lookup f arity)
