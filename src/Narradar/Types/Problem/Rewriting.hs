{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.Rewriting (Problem(..), Rewriting(..), IRewriting(..), rewritingProblem, irewritingProblem) where

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
import MuTerm.Framework.Problem.Types
import MuTerm.Framework.Proof

import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr

instance IsProblem Rewriting where
  data Problem Rewriting a = RewritingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = Rewriting
  getR (RewritingProblem r _) = r

instance IsDPProblem Rewriting where
  getP   (RewritingProblem _ p) = p

instance Monoid trs => MkProblem Rewriting trs where
  mkProblem Rewriting rr = rewritingProblem rr mempty
  mapR f (RewritingProblem r p) = RewritingProblem (f r) p


instance MkProblem Rewriting trs => MkDPProblem Rewriting trs where
  mkDPProblem Rewriting = rewritingProblem
  mapP f (RewritingProblem r p) = RewritingProblem r (f p)

instance (Unify t, HasId t, Enum v, Ord v, Pretty v, Ord (Term t v), Pretty (t(Term t v))) =>
  MkProblem Rewriting (NarradarTRS t v)
 where
  mkProblem Rewriting rr = rewritingProblem rr mempty
  mapR f (RewritingProblem rr pp) = mkDPProblem' Rewriting (f rr) pp

instance (Unify t, HasId t, Ord (Term t v), Enum v, Ord v, Pretty v, Pretty (t(Term t v))) =>
  MkDPProblem Rewriting (NarradarTRS t v)
 where
  mkDPProblem Rewriting rr dd@DPTRS{} = rewritingProblem rr dd
  mkDPProblem Rewriting rr dd = mkDPProblem' Rewriting rr dd
  mapP f (RewritingProblem rr pp) = case f pp of
                                    pp'@DPTRS{} -> RewritingProblem rr pp'
                                    pp' -> mkDPProblem' Rewriting rr pp'

instance IsProblem IRewriting where
  data Problem IRewriting a = IRewritingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = IRewriting
  getR (IRewritingProblem r _) = r

instance IsDPProblem IRewriting where
  getP (IRewritingProblem _ p) = p

instance Monoid trs => MkProblem IRewriting trs where
  mkProblem IRewriting rr = irewritingProblem rr mempty
  mapR f (IRewritingProblem r p) = IRewritingProblem (f r) p

instance MkProblem IRewriting trs => MkDPProblem IRewriting trs where
  mkDPProblem _ = irewritingProblem
  mapP f (IRewritingProblem r p) = IRewritingProblem r (f p)

instance (Unify t, HasId t, Enum v, Ord v, Pretty v, Ord (Term t v), Pretty (t(Term t v))) =>
  MkProblem IRewriting (NarradarTRS t v)
 where
  mkProblem IRewriting rr = irewritingProblem rr mempty
  mapR f (IRewritingProblem rr pp) = mkDPProblem' IRewriting (f rr) pp

instance (Unify t, HasId t, Ord (Term t v), Enum v, Ord v, Pretty v, Pretty (t(Term t v))) =>
  MkDPProblem IRewriting (NarradarTRS t v)
 where
  mkDPProblem IRewriting rr dd@DPTRS{} = irewritingProblem rr dd
  mkDPProblem IRewriting rr dd = mkDPProblem' IRewriting rr dd
  mapP f (IRewritingProblem rr pp) = case f pp of
                                    pp'@DPTRS{} -> IRewritingProblem rr pp'
                                    pp' -> mkDPProblem' IRewriting rr pp'

rewritingProblem         = RewritingProblem
irewritingProblem        = IRewritingProblem

-- Functor

instance Functor (Problem Rewriting)     where fmap f (RewritingProblem r p) = RewritingProblem (f r) (f p)
instance Foldable (Problem Rewriting)    where foldMap f (RewritingProblem r p) = f r `mappend` f p
instance Traversable (Problem Rewriting) where traverse f (RewritingProblem r p) = RewritingProblem <$> f r <*> f p

instance Functor (Problem IRewriting) where fmap f (IRewritingProblem r p) = IRewritingProblem (f r) (f p)
instance Foldable (Problem IRewriting) where foldMap f (IRewritingProblem r p) = f r `mappend` f p
instance Traversable (Problem IRewriting) where traverse f (IRewritingProblem r p) = IRewritingProblem <$> f r <*> f p

-- Data.Term


-- Output

instance Pretty Rewriting where pPrint _ = text "Rewriting"
instance Pretty IRewriting where pPrint _ = text "Innermost Rewriting"

instance HTML Rewriting where toHtml _ = toHtml "Rewriting Problem"
instance HTML IRewriting where toHtml _ = toHtml "Innermost Rewriting Problem"

instance HTMLClass Rewriting where htmlClass _ = theclass "DP"
instance HTMLClass IRewriting where htmlClass _ = theclass "IDP"

-- ICap

instance (Unify t, Ord v) => ICap t v (Rewriting, NarradarTRS t v) where icap (typ,trs) = icap (typ, rules trs)
instance (Unify t, Ord v) => ICap t v (IRewriting, NarradarTRS t v) where icap (typ,trs) = icap (typ, rules trs)

instance (Ord v, Unify t) => ICap t v (Rewriting, [Rule t v]) where
  icap (_,trs) = icap trs

instance (Ord v, Unify t) => ICap t v (IRewriting, [Rule t v]) where
  icap (_,trs) t = do
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
  iUsableRulesM p@(Rewriting, trs) tt = do
    trs' <- f_UsableRules p (iUsableRulesVarM p) =<< getFresh tt
    return (Rewriting, tRS $ toList trs')
  iUsableRulesVarM (_,trs) _ = return $ Set.fromList $ rules trs

instance (Ord (Term t v), Ord v, Unify t, HasId t) => IUsableRules t v (IRewriting, NarradarTRS t v) where
  iUsableRulesM p@(IRewriting, trs) tt = do
    trs' <- f_UsableRules p (iUsableRulesVarM p) =<< getFresh tt
    return (IRewriting, tRS $ toList trs')
  iUsableRulesVarM _ _ = return mempty

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
           let rr  = [ r | r <- rules trs, lhs r `unifies` t']
               new = Set.difference (Set.fromList rr) acc
           rhsSubterms <- getFresh (rhs <$> F.toList new)
           go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])


-- Insert Pairs

instance (Pretty id, Ord id) =>InsertDPairs Rewriting (NTRS id) where
  insertDPairs = insertDPairsDefault

instance (Pretty id, Ord id) =>InsertDPairs IRewriting (NTRS id) where
  insertDPairs = insertDPairsDefault
