{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}

module Narradar.Framework.Observe where

import Control.Monad.ConstrainedNormal (NF(..))
import Control.Monad.Free
import Control.Monad.Variant
import Control.Monad.List
import Data.Constraint -- ((:-)(..),Dict(..))
import Data.Constraint.Forall
import Data.Map (Map)
import Data.Set (Set)
import Data.AlaCarte
import Data.Graph
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Reflection
import Data.Term (MEnvT, Var)
import Language.Prolog.Representation
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy
import Narradar.Framework.Ppr
import Narradar.Types.Term
import Data.Functor.Constant (Constant(..))

import Debug.Hoed.Observe
import GHC.Generics(Generic)
import Data.Foldable (toList)
import Data.Term.Rules (RuleF(..))
import qualified Data.Term as Term


class ObservableVar1 t where
  observerVar1 :: (Observable x, Observable (Var x)) => t x -> Parent -> t x
  observersVar1 :: (Observable x, Observable (Var x)) => Parent -> String -> (Observer -> t x) -> t x

instance Observable1 f => ObservableVar1 f where
  observerVar1 = observer1
  observersVar1 = observers1
{-
instance (Observable a, Observable(Var a), ObservableVar1 f) => Observable (f a) where
  observer = observerVar1
  observers = observersVar1
-}
-- ---------------
-- Hood instances
-- ---------------
instance (Observable k) => Observable1 (Map k) where
  observer1 x p = Map.fromDistinctAscList $ fmap unLiftObserve1 $ observer1 (fmap LiftObserve1 $ Map.toList x) p
instance Observable1 Set where
  observer1 x p = Set.fromDistinctAscList (observer1 (Set.toList x) p)
deriving instance Generic (SCC a)
instance Observable1 SCC
--instance (Observable id) => Observable1 (TermF id)

--instance (Pretty (Term term var), Pretty var) => Observable (Substitution term var) where
--  observer s = send (show $ pPrint s) (return s)
instance Observable1 RuleF where observer1 (l :-> r) = send "(:->)" (return (:->) << l << r)

instance Observable (f(Expr f)) => (Observable (Expr f))
instance (Observable1 f, Observable1 g) => Observable1 (f :+: g)
instance (Observable a) => Observable1 (K a)
instance Observable PrologP_
instance Observable PrologT_
instance Observable id => Observable1 (T id)
instance Observable BS.ByteString where observer = observeBase -- send ("BS: " ++ show x) (return x)
deriving instance Generic (Constant a b)
instance (Observable a) => Observable1 (Constant a)
instance (Monad m) => Observable1 (MVariantT v m) where
  observer1 = observeComp "<MvariantT>"
instance (Monad m) => Observable1 (ListT m) where
  observer1 = observeComp "<ListT>"
instance Monad m => Observable1 (MEnvT  t v m) where observer1 = observeComp "<MEnvT>"

-- newtype WrapObserveM m a = WrapObserveM {unwrapObserveM :: m a} deriving (Observable, Observable1)
-- class ObserveM ma where observeM :: String -> ma -> ma
-- instance (Observable1 m, Observable a) => ObserveM (m a) where
--   observeM tag = unwrapObserveM . gdmobserve1 tag . WrapObserveM
-- instance (Observable1 m, Observable a) => ObserveM (b -> m a) where
--   observeM tag = (observeM tag .)
-- instance (Observable1 m, Observable a) => ObserveM (c -> b -> m a) where
--   observeM tag = ((observeM tag .).)
-- instance (Observable1 m, Observable a) => ObserveM (d -> c -> b -> m a) where
--   observeM tag = (((observeM tag .).).)
-- instance (Observable1 m, Observable a) => ObserveM (e -> d -> c -> b -> m a) where
--   observeM tag = ((((observeM tag .).).).)

-- not right, we can only observe the original value before it was fmapped !!
instance (Observable1 t) => Observable1 (NF GetVarsObservable t) where
  observer1 (FMap f t) p = FMap f (observer1 t p)

instance Observable1 (NF GetVarsObservable Substitution_) where
  observer1 (FMap f (Subst m)) = send "Subst" (return (FMap f . Subst) .<< m)

instance Observable Final

deriving instance Generic (EqModulo a)
instance Observable1 EqModulo

--instance (Observable x, Observable(Var x)) => Observable (SubstitutionF x) where
  --observer = observerVar1

--observeComp :: (Observable a, Monad m) => String -> m a -> Parent -> m a
observeComp name comp ctxt = do
    res <- comp
    send name (return return << res) ctxt

observeM :: (Observable b, Monad m) => Observer -> m b -> m b
observeM (O o oo) comp  = do
    res <- comp
    return (o "value" res)
