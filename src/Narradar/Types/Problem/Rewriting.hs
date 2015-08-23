{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module Narradar.Types.Problem.Rewriting
         ( MkRewriting(..), Problem(..), Rewriting, IRewriting, rewriting, irewriting
         ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Exception (assert)
import Data.Foldable as F (Foldable(..), toList)
import Data.Monoid
import Data.Traversable as T (Traversable(..), mapM)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import Text.XHtml (HTML(..), theclass)

import Data.Term
import qualified Data.Term.Family as Family
import Data.Term.Rules

import Narradar.Constraints.UsableRules
import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr

import GHC.Generics (Generic)
import Debug.Hoed.Observe

data MkRewriting strat = MkRewriting (Strategy strat) Minimality deriving (Eq, Ord, Show, Generic, Generic1, Typeable)

type Rewriting  = MkRewriting Standard
type IRewriting = MkRewriting Innermost

instance HasSignature (MkRewriting strat) where getSignature _ = mempty

rewriting  = MkRewriting Standard  M
irewriting = MkRewriting Innermost M

instance NFData strat => NFData (MkRewriting strat) where rnf (MkRewriting s m) = rnf s `seq` rnf m

instance GetPairs (MkRewriting strat) where getPairs = getPairsDefault

instance IsProblem (MkRewriting st) where
  data Problem (MkRewriting st) a = RewritingProblem {rr,dd :: a, st :: Strategy st, m :: Minimality}
                                  deriving (Eq, Ord, Show)
  getFramework (RewritingProblem _ _ s m) = MkRewriting s m
  getR (RewritingProblem r _ _ _) = r

instance HasSignature a => HasSignature (Problem (MkRewriting st) a) where
  getSignature p = getSignature (rr p) `mappend` getSignature (dd p)

instance IsDPProblem (MkRewriting st) where
  getP   (RewritingProblem _ p _ _) = p

instance (MkDPProblem (MkRewriting st) trs, Monoid trs) => MkProblem (MkRewriting st) trs where
  mkProblem (MkRewriting s m) rr = RewritingProblem rr mempty s m
  mapRO o f (RewritingProblem r p s m) = mkDPProblemO o (MkRewriting s m) (f r) p
  setR_uncheckedO _ rr p = p{rr}

instance MkProblem (MkRewriting st) trs => MkDPProblem (MkRewriting st) trs where
  mkDPProblemO o (MkRewriting s m) r p = RewritingProblem r p s m
  mapPO o f (RewritingProblem r p s m) = RewritingProblem r (f p) s m
  setP_uncheckedO _ dd p = p{dd}

instance (FrameworkN0 (MkRewriting st) t v) =>
  MkProblem (MkRewriting st) (NarradarTRS t v)
 where
  mkProblem (MkRewriting s m) rr = RewritingProblem rr mempty s m
  mapRO o f (RewritingProblem rr pp s m) = mkDPProblemO o (MkRewriting s m) (f rr) pp
  setR_uncheckedO _ rr p = p{rr}

instance ( FrameworkN0 (MkRewriting st) t v, Observable st ) =>
  MkDPProblem (MkRewriting st) (NarradarTRS t v)
 where
  mkDPProblemO (O o oo) it@(MkRewriting s m) rr dd
    = case lowerNTRS dd of
        pp@DPTRS{rulesUsed} | (Set.fromList $ rules rr) == rulesUsed -> RewritingProblem rr dd s m
        otherwise -> oo "dpTRS" dpTRSO (RewritingProblem rr dd s m)
  mapPO (O _ oo) f me@RewritingProblem{rr,dd} =
    let dd' = f dd in
    case lowerNTRS dd' of
      DPTRS{rulesUsed}
        | Set.fromList(rules rr) == rulesUsed -> me{dd=dd'}
      _ -> oo "dpTRS" dpTRSO me{dd=dd'}
  setP_uncheckedO _ dd p = p{dd}

-- Prelude

instance Eq (Strategy st) where
  Standard  == Standard  = True
  Innermost == Innermost = True
  _         == _         = False

instance Show (Strategy st) where
  show Standard = "Standard"
  show Innermost = "Innermost"

instance Ord (Strategy st) where
  compare Standard Standard = EQ
  compare Innermost Innermost = EQ
  compare Innermost _ = LT


isInnermost :: Strategy st -> Bool
isInnermost Innermost = True
isInnermost _         = False

instance NFData trs => NFData (Problem (MkRewriting st) trs) where
  rnf (RewritingProblem rr dd s m) = rnf rr `seq` rnf dd `seq` rnf s `seq` rnf m `seq` ()

-- Framework

instance HasStrategy Rewriting Standard   where getStrategy _ = Standard
instance HasStrategy IRewriting Innermost where getStrategy _ = Innermost

instance HasMinimality (MkRewriting st) where
    getMinimality    (MkRewriting st m) = m
    setMinimality m' (RewritingProblem rr dd s _) = RewritingProblem rr dd s m'

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
    pPrint (MkRewriting Innermost A) = text "Innermost Rewriting (no minimality)"


instance HTML Rewriting where
    toHtml (MkRewriting Standard  M) = toHtml "Rewriting Problem"
    toHtml (MkRewriting Standard  A) = toHtml "Rewriting Problem (no minimality)"
instance HTML IRewriting where
    toHtml (MkRewriting Innermost M) = toHtml "Innermost Rewriting Problem"
    toHtml (MkRewriting Innermost A) = toHtml "Innermost Rewriting Problem (no minimality)"


instance HTMLClass Rewriting  where htmlClass (MkRewriting Standard _) = theclass "DP"
instance HTMLClass IRewriting where htmlClass (MkRewriting Innermost _) = theclass "IDP"


instance (v ~ Family.Var trs
         ,t ~ Family.TermF trs
         ,Rule t v ~ Family.Rule trs
         ,Pretty v, PprTPDB v, Ord v
         ,HasRules trs, GetVars trs, Pretty (t(Term t v))
         ,HasId1 t, Pretty (Id t), Functor t, Foldable t
         ) => PprTPDB (Problem (MkRewriting st) trs) where
  pprTPDB prob@(RewritingProblem r p st m) = vcat
     [parens( text "VAR" <+> (fsep $ snub $ map pprTPDB $ toList $ getVars prob))
     ,parens( text "RULES" $$
              nest 1 (vcat $ map pprTPDB $ rules $ r))
     ,if not (null $ rules p)
         then parens( text "PAIRS" $$
              nest 1 (vcat $ map pprTPDB $ rules $ p))
         else Ppr.empty
     ,if isInnermost st then parens (text "STRATEGY INNERMOST") else Ppr.empty
     ,if m == M then parens (text "MINIMALITY") else Ppr.empty
     ]

-- ICap

instance (FrameworkTerm t v, Ord(Id t)
         ) => ICap (Problem (MkRewriting st) (NarradarTRS t v)) where
  icapO o p@RewritingProblem{st} s t
    | not(isInnermost st) = icapO o (getR p) s t
    | otherwise = do
#ifdef DEBUG
    when (not $ Set.null (getVars (getR p) `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` p
#else
    assert (Set.null (getVars (getR p) `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules $ getR p)
    let go t = if any (unifies (wrap t) . lhs) rr
                then return `liftM` freshVar else return (wrap t)
        doVar v = return2 v -- Do not rename vars
    foldTermM doVar go t

-- Usable Rules

instance (FrameworkN0 (MkRewriting st) t v
         ) => IUsableRules (Problem (MkRewriting st) (NarradarTRS t v)) where
  iUsableRulesM p s tt = do
    f_UsableRules p (iUsableRulesVarM p) s =<< getFresh tt

  iUsableRulesVarM p@(RewritingProblem trs _ st _) _ _
    | isInnermost st = return (setR mempty p)
    | otherwise      = return p

instance (FrameworkN0 (MkRewriting st) t v
         ,FrameworkN0 IRewriting t v
         ) => NeededRules (Problem (MkRewriting st) (NarradarTRS t v)) where
  neededRulesM p tt = do
    p' <- iUsableRulesM (mapFramework (const irewriting) p) [] tt
    return (setR (getR p') p)

-- Insert Pairs

instance (FrameworkProblemN (MkRewriting st) id
         ) => InsertDPairs (MkRewriting st) (NTRS id) where
  insertDPairsO = insertDPairsDefault

instance (FrameworkProblemN (MkRewriting st) id
         ) => ExpandDPair (MkRewriting st) (NTRS id) where
  expandDPairO = expandDPairOdefault

-- Hood

instance Observable1 MkRewriting
instance Observable a => Observable(MkRewriting a) where
  observer = observer1
  observers = observers1

instance Observable st => Observable1 (Problem (MkRewriting st)) where
  observer1 (RewritingProblem rr dd st m) =
    send "RewritingProblem"
    (return RewritingProblem << rr << dd << st << m)

instance (Observable st, Observable trs) => Observable(Problem(MkRewriting st) trs) where
  observer = observer1
  observers = observers1
