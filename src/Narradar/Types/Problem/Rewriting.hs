{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.Rewriting
         ( Problem(..), MkRewriting(..), Rewriting, IRewriting, rewriting, irewriting
         , Standard(..), Innermost(..), Minimality(..)
         , f_UsableRules
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

import MuTerm.Framework.Problem
--import MuTerm.Framework.Problem.Types
import MuTerm.Framework.Proof

import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr

data MkRewriting strat = MkRewriting strat Minimality deriving (Eq, Ord, Show)

type Rewriting  = MkRewriting Standard
type IRewriting = MkRewriting Innermost

data Standard  = Standard  deriving (Eq, Ord, Show)
data Innermost = Innermost deriving (Eq, Ord, Show)
data Minimality  = M | A   deriving (Eq, Ord, Show)

rewriting  = MkRewriting Standard  M
irewriting = MkRewriting Innermost M

instance IsProblem (MkRewriting st) where
  data Problem (MkRewriting st) a = RewritingProblem a a st Minimality deriving (Eq, Ord, Show)
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

instance (Unify t, Ord v) => ICap t v (Rewriting,  NarradarTRS t v) where icap (typ,trs) = icap (typ, rules trs)
instance (Unify t, Ord v) => ICap t v (IRewriting, NarradarTRS t v) where icap (typ,trs) = icap (typ, rules trs)
instance (Ord v, Unify t) => ICap t v (Rewriting, [Rule t v]) where
  icap (MkRewriting Standard  _, trs) t = icap trs t

instance (Ord v, Unify t) => ICap t v (IRewriting, [Rule t v]) where
  icap (MkRewriting Innermost _, trs) t = do
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

instance (Ord(Term t v), Ord v, Unify t, HasId t) => IUsableRules t v (Rewriting, NarradarTRS t v) where
--iUsableRulesM p _ tt | assert (Set.null (getVars p `Set.intersection` getVars tt)) False = undefined

  iUsableRulesM p@(m@(MkRewriting Standard _), trs) tt = do
    trs' <- f_UsableRules p (iUsableRulesVarM p) =<< getFresh tt
    return (m, tRS $ toList trs')

  iUsableRulesVarM (MkRewriting Standard _,trs) _ = return $ Set.fromList $ rules trs


instance (Ord(Term t v), Ord v, Unify t, HasId t) => IUsableRules t v (IRewriting, NarradarTRS t v) where
  iUsableRulesM p@(m@(MkRewriting Innermost _), trs) tt = do
    trs' <- f_UsableRules p (iUsableRulesVarM p) =<< getFresh tt
    return (m, tRS $ toList trs')

  iUsableRulesVarM (MkRewriting Innermost _, _) _ = return mempty

f_UsableRules :: forall term vk acc t v trs typ problem m.
                 ( Ord (Term t v), Unify t, Ord v
                 , problem ~ (typ, trs)
                 , term ~ Term t v
                 , vk ~ (v -> m acc)
                 , acc ~ Set (Rule t v)
                 , HasRules t v trs, GetVars v trs
                 , ICap t v problem
                 , MonadFresh v m
                 ) =>
                 problem -> vk -> [term] -> m acc
f_UsableRules p@(_,trs) _  tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRules p@(_,trs) vk tt = go mempty tt where
  go acc []       = return acc
  go acc (t:rest) = evalTerm (\v -> vk v >>= \vacc -> go (vacc `mappend` acc) rest) tk t where
        tk :: t (Term t v) -> m acc
        tk in_t = do
           t'  <- wrap `liftM` (icap p `T.mapM` in_t)
           let rr  = [ l:->r | l:->r <- rules trs, not(isVar l), l `unifies` t']
               new = Set.difference (Set.fromList rr) acc
           rhsSubterms <- getFresh (rhs <$> F.toList new)
           go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])


-- Insert Pairs

instance (Pretty id, Ord id) =>InsertDPairs Rewriting  (NTRS id) where insertDPairs = insertDPairsDefault
instance (Pretty id, Ord id) =>InsertDPairs IRewriting (NTRS id) where insertDPairs = insertDPairsDefault
