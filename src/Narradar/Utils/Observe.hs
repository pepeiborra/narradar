{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Narradar.Utils.Observe where

import Control.Monad.Variant
import Control.Monad.List
import Data.Map (Map)
import Data.Set (Set)
import Data.AlaCarte
import Data.Graph
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Term (Substitution)
import Language.Prolog.Representation
import MuTerm.Framework.Proof
import MuTerm.Framework.Strategy
import Narradar.Types.Term
import Narradar.Framework.Ppr
import Data.Functor.Constant (Constant(..))

import Debug.Hoed.Observe
import GHC.Generics(Generic)

-- ---------------
-- Hood instances
-- ---------------
instance (Observable k) => Observable1 (Map k) where
  observer1 x p = Map.fromDistinctAscList (observer (Map.toList x) p)
instance Observable1 Set where
  observer1 x p = Set.fromDistinctAscList (observer (Set.toList x) p)
deriving instance Generic (SCC a)
instance Observable1 SCC
--instance (Observable id) => Observable1 (TermF id)

instance Observable id => Observable1 (TermF id) where observer1 (Term id tt) = send "" (return Term << id .<< tt)

instance Observable1 ArityId
instance Observable1 RuleF where observer1 (l :-> r) = send "(:->)" (return (:->) << l << r)
deriving instance Generic (SubstitutionF v a)
instance Observable var => Observable1 (SubstitutionF var)
--instance (Pretty (Term term var), Pretty var) => Observable (Substitution term var) where
--  observer s = send (show $ pPrint s) (return s)
deriving instance Generic (Free f v)
instance Observable1 f => Observable1 (Free f) where
  observer1 (Pure t)   = Pure . observer t
  observer1 (Impure t) = Impure . observer t
instance (Pretty(TermN id)) => Observable (TermN id) where observer t = t `seq` send (show$ pPrint t) (return t)
instance Observable (f(Expr f)) => (Observable (Expr f))
instance (Observable1 f, Observable1 g) => Observable1 ((f :+: g))
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
instance Monad m => Observable1 (MEnvT t v m) where observer1 = observeComp "<MEnvT>"

instance (Monad m, Observable1 m) => Observable1 (ProofF info m) where
  observer1 (And    pi p pp) = send "And" (return (And pi p) << pp)
  observer1 (Or     pi p pp) = send "Or"  (return (Or  pi p) .<< pp)
  observer1 (Single pi p k ) = send "Single"   (return (Single pi p) << k)
  observer1 (DontKnow pi p)  = send "DontKnow" (return $ DontKnow pi p)
  observer1 (Success  pi p)  = send "Success"  (return $ Success  pi p)
  observer1 (Search mk)      = send "Search"   (return Search .<<  mk)

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

instance Observable Final

deriving instance Generic (EqModulo a)
instance Observable1 EqModulo

--observeComp :: (Observable a, Monad m) => String -> m a -> parent -> m a
observeComp name comp ctxt = do
    res <- comp
    send name (return return << res) ctxt

observe x = gdmobserve x
