{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.Rewriting where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.Free
import Data.Foldable as F (Foldable(..), toList)
import Data.Traversable as T (Traversable(..), mapM)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Text.XHtml (HTML(..), theclass)

import Data.Term
import Data.Term.Rules

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework.Ppr

data Rewriting = Rewriting                          deriving (Eq, Ord, Show)
instance IsDPProblem Rewriting where
  data DPProblem Rewriting a = RewritingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = Rewriting
  mkDPProblem    _ = rewritingProblem
  getR (RewritingProblem r _) = r
  getP (RewritingProblem _ p) = p
  mapR f (RewritingProblem r p) = RewritingProblem (f r) p
  mapP f (RewritingProblem r p) = RewritingProblem r (f p)

data IRewriting = IRewriting                          deriving (Eq, Ord, Show)
instance IsDPProblem IRewriting where
  data DPProblem IRewriting a = IRewritingProblem a a deriving (Eq, Ord, Show)
  getProblemType _ = IRewriting
  mkDPProblem    _ = iRewritingProblem
  getR (IRewritingProblem r _) = r
  getP (IRewritingProblem _ p) = p
  mapR f (IRewritingProblem r p) = IRewritingProblem (f r) p
  mapP f (IRewritingProblem r p) = IRewritingProblem r (f p)

rewritingProblem         = RewritingProblem
iRewritingProblem        = IRewritingProblem

-- Functor

instance Functor (DPProblem Rewriting) where fmap f (RewritingProblem r p) = RewritingProblem (f r) (f p)
instance Foldable (DPProblem Rewriting) where foldMap f (RewritingProblem r p) = f r `mappend` f p
instance Traversable (DPProblem Rewriting) where traverse f (RewritingProblem r p) = RewritingProblem <$> f r <*> f p

instance Functor (DPProblem IRewriting) where fmap f (IRewritingProblem r p) = IRewritingProblem (f r) (f p)
instance Foldable (DPProblem IRewriting) where foldMap f (IRewritingProblem r p) = f r `mappend` f p
instance Traversable (DPProblem IRewriting) where traverse f (IRewritingProblem r p) = IRewritingProblem <$> f r <*> f p

-- Output

instance Pretty Rewriting where pPrint _ = text "Rewriting"
instance Pretty IRewriting where pPrint _ = text "Innermost Rewriting"

instance HTML Rewriting where toHtml _ = toHtml "Rewriting Problem"
instance HTML IRewriting where toHtml _ = toHtml "Innermost Rewriting Problem"

instance HTMLClass Rewriting where htmlClass _ = theclass "DP"
instance HTMLClass IRewriting where htmlClass _ = theclass "IDP"


-- Construction

instance Ord id => MkNarradarProblem Rewriting (TermF id) where
  type ProblemType Rewriting (TermF id) = Rewriting
  type TermType    Rewriting (TermF id) = TermF (Identifier id)
  mkNarradarProblem = mkNarradarProblemDefault

instance Ord id => MkNarradarProblem IRewriting (TermF id) where
  type ProblemType IRewriting (TermF id) = IRewriting
  type TermType    IRewriting (TermF id) = TermF (Identifier id)
  mkNarradarProblem = mkNarradarProblemDefault

-- ICap

instance (HasRules t v trs, GetVars v trs, Unify t, ICap t v trs) => ICap t v (Rewriting, trs) where icap (_,trs) = icap trs


instance (HasRules t v trs, Unify t, GetVars v trs) => ICap t v (IRewriting, trs) where
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

instance (Ord(Term t v), Unify t, IsTRS t v trs, GetVars v trs, ICap t v trs) => IUsableRules t v (Rewriting, trs) where
--iUsableRulesM p _ tt | assert (Set.null (getVars p `Set.intersection` getVars tt)) False = undefined
  iUsableRulesM p@(Rewriting, trs) tt = do
    trs' <- f_UsableRules p (iUsableRulesVar p) =<< getFresh tt
    return (Rewriting, trs)
  iUsableRulesVar (_,trs) _ = Set.fromList $ rules trs

instance (Enum v, Ord (Term t v), Unify t, IsTRS t v trs, GetVars v trs) => IUsableRules t v (IRewriting, trs) where
  iUsableRulesM p@(IRewriting, trs) tt = do
    trs' <- f_UsableRules p (iUsableRulesVar p) =<< getFresh tt
    return (IRewriting, tRS $ toList trs')
  iUsableRulesVar _ _ = mempty

f_UsableRules :: forall term vk acc t v trs typ problem m.
                 ( Ord (Term t v), Unify t, Ord v
                 , problem ~ (typ, trs)
                 , term ~ Term t v
                 , vk ~ (v -> acc)
                 , acc ~ Set (Rule t v)
                 , HasRules t v trs, GetVars v trs
                 , ICap t v problem
                 , MonadFresh v m
                 ) =>
                 problem -> vk -> [term] -> m acc
f_UsableRules p@(_,trs) _  tt | assert (Set.null (getVars trs `Set.intersection` getVars tt)) False = undefined
f_UsableRules p@(_,trs) vk tt = go mempty tt where
  go acc []       = return acc
  go acc (t:rest) = evalTerm (\v -> go (vk v `mappend` acc) rest) tk t where
        tk :: t (Term t v) -> m acc
        tk in_t = do
           t'  <- wrap `liftM` (icap p `T.mapM` in_t)
           let rr  = [ r | r <- rules trs, lhs r `unifies` t']
               new = Set.difference (Set.fromList rr) acc
           rhsSubterms <- getFresh (rhs <$> F.toList new)
           go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])

