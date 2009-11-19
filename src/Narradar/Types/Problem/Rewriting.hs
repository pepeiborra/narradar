{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.Rewriting
         ( Problem(..), MkRewriting(..), Rewriting, IRewriting, rewriting, irewriting
         , Strategy(..), HasStrategy(..), Standard, Innermost, isInnermost
         , Minimality(..), HasMinimality(..), getMinimalityFromProblem
         ) where

import Control.Applicative
import Control.Monad
import Control.Exception (assert)
import Data.Foldable as F (Foldable(..), toList)
import Data.Monoid
import Data.Traversable as T (Traversable(..), mapM)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.XHtml (HTML(..), theclass)

import Data.Term
import Data.Term.Rules

import Narradar.Constraints.UsableRules
import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework
import Narradar.Framework.Ppr

data MkRewriting strat = MkRewriting (Strategy strat) Minimality deriving (Eq, Ord, Show)

type Rewriting  = MkRewriting Standard
type IRewriting = MkRewriting Innermost

data Standard
data Innermost
data Strategy st where
    Standard  :: Strategy Standard
    Innermost :: Strategy Innermost

data Minimality  = M | A   deriving (Eq, Ord, Show)

rewriting  = MkRewriting Standard  M
irewriting = MkRewriting Innermost M

instance IsProblem (MkRewriting st) where
  data Problem (MkRewriting st) a = RewritingProblem a a (Strategy st) Minimality deriving (Eq, Ord, Show)
  getProblemType (RewritingProblem _ _ s m) = MkRewriting s m
  getR (RewritingProblem r _ _ _) = r

instance IsDPProblem (MkRewriting st) where
  getP   (RewritingProblem _ p _ _) = p

instance Monoid trs => MkProblem (MkRewriting st) trs where
  mkProblem (MkRewriting s m) rr = RewritingProblem rr mempty s m
  mapR f (RewritingProblem r p s m) = RewritingProblem (f r) p s m


instance MkProblem (MkRewriting st) trs => MkDPProblem (MkRewriting st) trs where
  mkDPProblem (MkRewriting s m) r p = RewritingProblem r p s m
  mapP f (RewritingProblem r p s m) = RewritingProblem r (f p) s m

instance (Unify t, HasId t, Enum v, Ord v, Pretty v, Ord (Term t v), Pretty (t(Term t v))) =>
  MkProblem Rewriting (NarradarTRS t v)
 where
  mkProblem (MkRewriting s m) rr = RewritingProblem rr mempty s m
  mapR f (RewritingProblem rr pp s m) = mkDPProblem' (MkRewriting s m) (f rr) pp

instance (Unify t, HasId t, Enum v, Ord v, Pretty v, Ord (Term t v), Pretty (t(Term t v))) =>
  MkProblem IRewriting (NarradarTRS t v)
 where
  mkProblem (MkRewriting s m) rr = RewritingProblem rr mempty s m
  mapR f (RewritingProblem rr pp s m) = mkDPProblem' (MkRewriting s m) (f rr) pp

instance (Unify t, HasId t, Ord (Term t v), Enum v, Ord v, Pretty v, Pretty (t(Term t v))) =>
  MkDPProblem Rewriting (NarradarTRS t v)
 where
  mkDPProblem (MkRewriting s m) rr dd@DPTRS{} = RewritingProblem rr dd s m
  mkDPProblem it@(MkRewriting s m) rr dd = mkDPProblem' it rr dd
  mapP f (RewritingProblem rr pp s m) = case f pp of
                                          pp'@DPTRS{} -> RewritingProblem rr pp' s m
                                          pp' -> mkDPProblem' (MkRewriting s m) rr pp'

instance (Unify t, HasId t, Ord (Term t v), Enum v, Ord v, Pretty v, Pretty (t(Term t v))) =>
  MkDPProblem IRewriting (NarradarTRS t v)
 where
  mkDPProblem (MkRewriting s m) rr dd@DPTRS{} = RewritingProblem rr dd s m
  mkDPProblem it@(MkRewriting s m) rr dd = mkDPProblem' it rr dd
  mapP f (RewritingProblem rr pp s m) = case f pp of
                                          pp'@DPTRS{} -> RewritingProblem rr pp' s m
                                          pp' -> mkDPProblem' (MkRewriting s m) rr pp'

-- The HasStrategy and HasMinimality classes

class IsDPProblem typ => HasStrategy typ st | typ -> st where
  getStrategy :: typ -> Strategy st

instance HasStrategy Rewriting Standard   where getStrategy _ = Standard
instance HasStrategy IRewriting Innermost where getStrategy _ = Innermost

instance (FrameworkExtension ext, IsDPProblem (ext b), HasStrategy b st) => HasStrategy (ext b) st where
  getStrategy = getStrategy . getBaseFramework

class IsDPProblem typ => HasMinimality typ where
  getMinimality :: typ -> Minimality
  setMinimality :: Minimality -> Problem typ trs -> Problem typ trs

getMinimalityFromProblem :: HasMinimality typ => Problem typ trs -> Minimality
getMinimalityFromProblem = getMinimality . getProblemType

instance HasMinimality (MkRewriting st) where
    getMinimality    (MkRewriting st m) = m
    setMinimality m' (RewritingProblem rr dd s _) = RewritingProblem rr dd s m'

instance (IsDPProblem (p b), HasMinimality b, FrameworkExtension p) => HasMinimality (p b)
   where getMinimality = getMinimality . getBaseFramework
         setMinimality m = liftFramework (setMinimality m)

-- Prelude

instance Eq (Strategy st) where
  Standard  == Standard  = True
  Innermost == Innermost = True
  _         == _         = False

instance Show (Strategy st) where
  show Standard = "Standard"
  show Innermost = "Innermost"

instance Ord (Strategy st) where
  compare Standard Innermost = GT
  compare Innermost Standard = LT
  compare x y = EQ

isInnermost :: Strategy st -> Bool
isInnermost Innermost = True
isInnermost _         = False

-- Functor

instance Functor (Problem (MkRewriting st))     where fmap     f (RewritingProblem r p s m) = RewritingProblem (f r) (f p) s m
instance Foldable (Problem (MkRewriting st))    where foldMap  f (RewritingProblem r p _ _) = f r `mappend` f p
instance Traversable (Problem (MkRewriting st)) where traverse f (RewritingProblem r p s m) = RewritingProblem <$> f r <*> f p <*> pure s <*> pure m


-- Output

instance Pretty Rewriting where
    pPrint (MkRewriting Standard M) = text "Rewriting"
    pPrint (MkRewriting Standard A) = text "Rewriting (no minimality)"
instance Pretty IRewriting where
    pPrint (MkRewriting Innermost M) = text "Innermost Rewriting"
    pPrint (MkRewriting Innermost A) = text "Innermost (MkRewriting st) (no minimality)"


instance HTML Rewriting where
    toHtml (MkRewriting Standard  M) = toHtml "Rewriting Problem"
    toHtml (MkRewriting Standard  A) = toHtml "Rewriting Problem (no minimality)"
instance HTML IRewriting where
    toHtml (MkRewriting Innermost M) = toHtml "Innermost Rewriting Problem"
    toHtml (MkRewriting Innermost A) = toHtml "Innermost Rewriting Problem (no minimality)"


instance HTMLClass Rewriting  where htmlClass (MkRewriting Standard _) = theclass "DP"
instance HTMLClass IRewriting where htmlClass (MkRewriting Innermost _) = theclass "IDP"

-- ICap

instance (Unify t, Ord v) => ICap t v (MkRewriting st, NarradarTRS t v) where icap (typ,trs) = icap (typ, rules trs)
instance (Ord v, Unify t) => ICap t v (MkRewriting st, [Rule t v]) where
  icap (MkRewriting st m, trs) t
    | not(isInnermost st) = icap trs t 
    | otherwise = do
#ifdef DEBUG
    when (not $ Set.null (getVars trs `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` trs
#else
    assert (Set.null (getVars trs `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules trs)
    let go t = if any (unifies (Impure t) . lhs) rr
                then return `liftM` freshVar else return (Impure t)
        doVar v = return2 v
    foldTermM doVar go t

-- Usable Rules

instance (Ord(Term t v), Ord v, Unify t, HasId t) => IUsableRules t v (MkRewriting st) (NarradarTRS t v) where
  iUsableRulesM m trs dps tt = do
    trs' <- f_UsableRules (m,trs) (iUsableRulesVarM m trs dps) =<< getFresh tt
    return (tRS $ toList trs')

  iUsableRulesVarM m@(MkRewriting st _) trs _ _
    | isInnermost st = return Set.empty
    | otherwise      = return $ Set.fromList $ rules trs

instance (Ord(Term t v), Ord v, Unify t, HasId t) => IUsableRules t v Rewriting [Rule t v] where
  iUsableRulesM    = deriveUsableRulesFromTRS (proxy :: Proxy (NarradarTRS t v))
  iUsableRulesVarM = deriveUsableRulesVarFromTRS (proxy :: Proxy (NarradarTRS t v))

instance (Ord(Term t v), Ord v, Unify t, HasId t) => IUsableRules t v IRewriting [Rule t v] where
  iUsableRulesM    = deriveUsableRulesFromTRS (proxy :: Proxy (NarradarTRS t v))
  iUsableRulesVarM = deriveUsableRulesVarFromTRS (proxy :: Proxy (NarradarTRS t v))

-- Insert Pairs

instance (Pretty id, Ord id) =>InsertDPairs Rewriting  (NTRS id) where insertDPairs = insertDPairsDefault
instance (Pretty id, Ord id) =>InsertDPairs IRewriting (NTRS id) where insertDPairs = insertDPairsDefault
