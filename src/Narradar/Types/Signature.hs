{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Narradar.Types.Signature
       (module Data.Term.Rules
       ,module Narradar.Types.Signature
       ) where

import Control.Monad.ConstrainedNormal
import Data.Constraint (Dict(..), (:-)(..))
import Data.Term.Rules
import qualified Data.Map as Map
import Narradar.Framework.Constraints

type SignatureF constraint a = NF constraint Signature a

lowerSignature :: forall c a . (c :=># Ord, Ord a) => SignatureF c a -> Signature a
lowerSignature = lowerNF (fmapSignature ins) where
  fmapSignature :: forall x . c x =>
                   c x :- Ord x -> (x -> a) -> Signature x -> Signature a
  fmapSignature (Sub Dict) f (Sig c d) = Sig (Map.mapKeys f c) (Map.mapKeys f d)
