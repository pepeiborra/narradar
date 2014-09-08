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

import Control.Applicative
import Control.Monad.ConstrainedNormal (NF(..))
import Control.Monad.Free
import Control.Monad.Variant
import Control.Monad.List
import Data.Constraint -- ((:-)(..),Dict(..))
import Data.Constraint.Forall
import Data.Map (Map)
import Data.Set (Set)
import Data.AlaCarte
import Data.Graph(SCC(..))
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Term (MEnvT, Var)
import Language.Prolog.Representation
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy
import Narradar.Framework.Ppr
import Narradar.Types.Term
import Data.Functor.Constant (Constant(..))
import Text.Parsec.Error(ParseError(..))
import Prelude.Extras

import Debug.Hoed.Observe
import GHC.Generics(Generic)
import Data.Foldable (toList)
import Data.Term.Rules (RuleF(..))
import Data.Term.Automata (TermMatcher(..), Tree(..))
import qualified Data.Term as Term


loo :: (Observable1 f, Observable a) => Observer -> String -> (Observer -> f a) -> f a
loo (O o oo) label x = lower1 $ oo label (Lift1 . x)

{-
instance Applicative f => Applicative (Lift1 f) where
  pure = Lift1 . pure
  Lift1 f <*> Lift1 x = Lift1 (f <*> x)

loo2 :: (Observable1 f, Observable1 g, Observable a, Observable b) => Observer -> String -> (Observer -> f a -> g b) -> f a -> g b
loo2 (O o oo) label x a = lower1 $ oo label (\o a -> Lift1 $ x o (lower1 a)) (Lift1 a)

loo3 :: (Observable1 f, Observable1 g, Observable1 h, Observable a, Observable b, Observable c
        ) => Observer -> String -> (Observer -> f a -> g b -> h c) -> f a -> g b -> h c
loo3 (O o oo) label x a b = lower1 $ oo label (\o a b -> Lift1 $ x o (lower1 a) (lower1 b)) (Lift1 a) (Lift1 b)

class Obs1 p where
  type Obs1Typ p :: *
  obsmake :: p -> Obs1Typ p
  obsap   :: Obs1Typ p -> p

loo :: Obs1 p => Observer -> String -> (Observer -> p) -> p
loo (O o oo) label p = lower1 $ 
-}

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
deriving instance Generic (SCC a)
deriving instance Generic1 SCC
instance Observable1 SCC
instance Observable a => Observable (SCC a) where
  observers = observers1
  observer = observer1
--instance (Observable id) => Observable1 (TermF id)

--instance (Pretty (Term term var), Pretty var) => Observable (Substitution term var) where
--  observer s = send (show $ pPrint s) (return s)
instance (Observable1 f, Observable1 g) => Observable1 ((f :+: g)) where
  observer1 (Inl f) ctxt = Inl (observer1 f ctxt)
  observer1 (Inr f) ctxt = Inr (observer1 f ctxt)
instance (Observable a, Observable1 f, Observable1 g) => Observable ((f :+: g) a) where
  observer = observer1
  observers = observers1
instance (Observable a) => Observable1 (K a)
instance (Observable a, Observable b) => Observable (K a b) where
  observer = observer1
  observers = observers1
instance Observable PrologP_
instance Observable PrologT_
instance Observable id => Observable1 (T id)
instance (Observable a, Observable id) => Observable(T id a) where
  observer = observer1
  observers = observers1
instance Observable BS.ByteString where observer = observeBase -- send ("BS: " ++ show x) (return x)
deriving instance Generic (Constant a b)
deriving instance Generic1 (Constant a)
instance (Observable a) => Observable1 (Constant a)
instance (Observable a, Observable b) => Observable (Constant a b) where
  observer = observer1
  observers = observers1

instance Observable1 f => Observable (Expr f) where
  observer (In fe) = send "In" (return In .<< fe)

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

instance (Observable a, Observable1 t) => Observable(NF GetVarsObservable t a) where
  observer = observer1
  observers = observers1

instance Observable Final

deriving instance Generic1 EqModulo
instance Observable1 EqModulo
instance Observable a => Observable (EqModulo a) where
  observer = observer1
  observers = observers1

instance Observable ParseError where observer = observeOpaque "ParseError"

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
