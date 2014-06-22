{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.QRewriting
         ( QRewriting(..), QRewritingN, qrewriting, QSet(..)
         , Problem(..)
         , inQNF, isQInnermost
         , qCondition, qCondition', isQValid
--         , Strategy(..), HasStrategy(..), Standard, Innermost, isInnermost
--         , Minimality(..), HasMinimality(..), getMinimalityFromProblem
         ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Exception (assert)
import Data.Foldable as F (Foldable(..), toList)
--import Data.MemoUgly
import Narradar.Utils.Memo
import Data.Monoid
import Data.Traversable as T (Traversable(..), mapM)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Rule.Family as Family
import qualified Data.Term.Family as Family
import Data.Term.Rewriting (isNF, rewrites)
import Data.Typeable
import Text.XHtml (HTML(..), theclass)

import Data.Term
import Data.Term.Rules
import qualified Data.Term.Family as Family

import Narradar.Constraints.UsableRules
import Narradar.Types.Problem
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils (return2, snub, pprTrace, none)
import Narradar.Utils.Observe
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr

import GHC.Generics (Generic)
import Debug.Hoed.Observe

newtype QSet term = QSet {qset :: [term]} deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Typeable)

instance NFData term => NFData (QSet term) where rnf (QSet tt) = rnf tt
instance Observable1 QSet
instance (HasSignature [term], Ord(Family.Id term)) => HasSignature (QSet term) where getSignature (QSet q) = getSignature q
instance Pretty term => Pretty (QSet term) where pPrint (QSet tt) = "QSet:" <+> fsep tt
type instance Family.TermF (QSet term) = Family.TermF term
type instance Family.Id    (QSet term) = Family.Id    term
type instance Family.Var   (QSet term) = Family.Var   term

{-
  The Q-condition to determine whether NF(Q) \subseteq NF(R) is expensive to compute.
  We can cache it once we construct a (DP) Problem, but that is too late.
  It comes up mostly when computing the usable rules for the inverse unifiers, in the DPTRS construction,
  which is a prerequisite step for creating a DP problem.

  I see four options:
    1. Generalize dpTRS, the constructor for DPTRS, to take problems instead of (typ,trs) pairs
    2. Have a heavily custom implementation of mkDPProblem for Q-Rewriting
    3. memoize mkQCondition
    4. Not use the inverse unifiers in DPTRS, instead compute them fresh in the Graph processor


  (1) seems like the most elegant approach but also the most costly
  (2) seems to involve inlining all the code for constructing a DPTRS, so not great
  (3) is the cheapest, good for prototyping
  (4) has a runtime penalty in that the unifiers get recomputed every time we apply the Graph processor. Probably not a big deal in practice.
      also seems to involve duplicadtion of compute Inverse Unifiers

 -}

-- | NF(Q) \subseteq NF(R)
mkQCondition :: (FrameworkTRS trs, Pretty trs
                ) => QSet (TermFor trs) -> trs -> Bool
mkQCondition = curry $ {-memo $-} \ (QSet qt, trs) -> none (isNF [ q :-> q | q <- qt]) (lhs <$> rules trs)

-- | NF(R) \subseteq NF(Q)
qCondition' (QSet qt) trs = none (isNF trs) qt

inQNF :: ( Ord v, Enum v, Rename v, Observable(Term t v)
         , Match t, Traversable t) =>
         Term t v -> QSet (Term t v) -> Bool
inQNF t (QSet qt) = isNF [ q :-> q | q <- qt] t 

data QRewriting term = QRewriting (QSet term) Minimality deriving (Eq, Ord, Show, Functor, Generic, Typeable)

type QRewritingN id = QRewriting (TermN id)

qrewriting = QRewriting (QSet []) M

instance GetPairs (QRewriting term) where getPairs = getPairsDefault

instance IsProblem (QRewriting id) where
  data Problem (QRewriting term) a = QRewritingProblem a a (QSet term) Minimality {-qCondition-} Bool
                                 deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
  getFramework (QRewritingProblem _ _ q m _) = QRewriting q m
  getR (QRewritingProblem r _ _ _ _) = r

isQInnermost = qCondition
qCondition (QRewritingProblem _ _ _ _ qC) = qC
isQValid   (QRewritingProblem trs _ q _ _) = qCondition' q (rules trs)

instance IsDPProblem (QRewriting id) where
  getP   (QRewritingProblem _ p _ _ _) = p

instance (MkDPProblem (QRewriting term) trs
         ,FrameworkProblem (QRewriting term) trs
         ,term ~ TermFor trs
         ,Family.Rule trs ~ RuleFor trs
         ,Pretty trs
         ) => MkProblem (QRewriting term) trs where
  mkProblem (QRewriting q m) rr = QRewritingProblem rr mempty q m (mkQCondition q rr)
  mapR f (QRewritingProblem r p s m qC) = mkDPProblem (QRewriting s m) (f r) p
{-
instance (MkProblem (QRewriting st) trs, Observable trs) => MkDPProblem (QRewriting st) trs where
  mkDPProblemO (O o oo) (QRewriting s m) r p   = QRewritingProblem (o "r" r) (o "p" p) s m
  mapP f (QRewritingProblem r p s m) = QRewritingProblem r (f p) s m
-}
instance (HasSignature trs, HasSignature [term], Family.Id term ~ Family.Id trs) => HasSignature (Problem (QRewriting term) trs) where
  getSignature (QRewritingProblem r p q _ _)  = getSignature r `mappend` getSignature p `mappend` getSignature q

instance (FrameworkTerm t v, Pretty(NarradarTRS t v)) =>
  MkProblem (QRewriting (Term t v)) (NarradarTRS t v)
 where
  mkProblem (QRewriting q m) rr = QRewritingProblem rr mempty q m (mkQCondition q rr)
  mapR f (QRewritingProblem rr pp s m _) = mkDPProblem (QRewriting s m) (f rr) pp

instance (FrameworkTerm t v, Pretty(NarradarTRS t v)) =>
  MkDPProblem (QRewriting (Term t v)) (NarradarTRS t v)
 where
--  mkDPProblem it@(QRewriting s m) rr dd | pprTrace (text "mkDPProblem rewriting with rules" $$ nest 2 rr) False = undefined
  mkDPProblemO (O o oo) it@(QRewriting q m) rr dd
    = case dd of
        pp@DPTRS{typ,rulesUsed} | o "typ == typ'" (typ == Comparable it) &&
                                  o "rules == rules'" (rr == rulesUsed)
                  -> QRewritingProblem rr dd q m (mkQCondition q rr)
        otherwise -> QRewritingProblem rr (oo "dpTRS" dpTRSO it rr dd) q m (mkQCondition q rr)
  mapP f (QRewritingProblem rr pp q m qC)
    = case f pp of
        pp'@DPTRS{typ,rulesUsed}
          | Comparable mytyp == typ && rr == rulesUsed
            -> QRewritingProblem rr pp' q m qC
        pp' -> QRewritingProblem rr (dpTRS mytyp rr pp') q m qC
    where mytyp = QRewriting q m

-- Prelude

instance (NFData term, NFData trs) => NFData (Problem (QRewriting term) trs) where
  rnf (QRewritingProblem rr dd s m qC) = rnf rr `seq` rnf dd `seq` rnf s `seq` rnf m `seq` rnf qC `seq` ()

-- Framework

instance HasMinimality (QRewriting st) where
    getMinimality    (QRewriting st m) = m
    setMinimality m' (QRewritingProblem rr dd s _ qC) = QRewritingProblem rr dd s m' qC

-- Functor


-- Output

instance Pretty term => Pretty (QRewriting term) where
    pPrint (QRewriting tt M) = text "Q-Rewriting"
    pPrint (QRewriting tt A) = text "Q-Rewriting (no minimality)"

instance Pretty term => HTML (QRewriting term) where
    toHtml (QRewriting tt M) = toHtml "Q-Rewriting Problem"
    toHtml (QRewriting tt A) = toHtml "Q-Rewriting Problem (no minimality)"

instance HTMLClass (QRewriting term) where htmlClass (QRewriting tt m) = theclass "QDP"


instance (HasRules trs, GetVars trs, Pretty v, PprTPDB v, Pretty (t(Term t v)), Ord v
         , Family.Rule trs ~ Rule t v
         , Family.Var  trs ~ v
         , Functor t, Foldable t, HasId t, Pretty (Id t)
         ) => PprTPDB (Problem (QRewriting (Term t v)) trs) where
  pprTPDB prob@(QRewritingProblem r p (QSet q) m _) = vcat
     [parens( text "VAR" <+> (fsep $ snub $ map pprTPDB $ toList $ getVars prob))
     ,parens( text "RULES" $$
              nest 1 (vcat $ map pprRule $ rules $ r))
     ,if not (null $ rules p)
         then parens( text "PAIRS" $$
              nest 1 (vcat $ map pprRule $ rules $ p))
         else Ppr.empty
     , parens (text "STRATEGY Q" <+> fsep (map pprTermTPDB q))
     ,if m == M then parens (text "MINIMALITY") else Ppr.empty
     ]
   where
        pprRule (a:->b) = pprTermTPDB a <+> text "->" <+> pprTermTPDB b


-- ICap
instance FrameworkTerm t v => ICap (QRewriting (Term t v), NarradarTRS t v) where
  icapO o (typ,trs) = icapO o (typ, rules trs)
instance FrameworkTerm t v => ICap (QRewriting (Term t v), [Rule t v]) where
--  icap (_,rules -> []) s t = return t
  icapO (O o oo) (QRewriting q m, trs) s t = do
#ifdef DEBUG
    when (not $ Set.null (getVars trs `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` trs
#else
    assert (Set.null (getVars trs `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules trs)
    let goO (O o oo) t =
          if and [ or [ not(o "inQNF" inQNF t q)
                              | t <- map (applySubst sigma) s ++ directSubterms (applySubst sigma l)]
                  | l :-> r <- rr
                  , Just sigma <- [o "unify" unify (Impure t) l] ]
                   then return (Impure t) else return `liftM` freshVar
        doVar v = if mkQCondition q trs && return v `elem` (concatMap subterms s)
                    then return2 v
                    else return `liftM` renaming v
    foldTermM doVar (oo "go" goO) t

-- Usable Rules
instance (FrameworkTerm t v, Pretty(NarradarTRS t v)
         ) => IUsableRules (QRewriting (Term t v)) (NarradarTRS t v) where
  iUsableRulesVarM (QRewriting q _) trs _dps _s _
    | mkQCondition q trs = return Set.empty
    | otherwise      = return $ Set.fromList $ rules trs
  iUsableRulesM = 
  -- gdmobservers "iUsableRules" $ \(O o oo) ->
   let o _ = id;
       oo :: String -> (Observer -> a) -> a
       oo _ f = f (O o oo) in
   \m@(QRewriting q _) trs dps s tt ->
--    pprTrace ("Q-Usable Rules" <+> tt) $
    let p  = mkDPProblem m trs dps

        go acc [] = return $ Set.map eqModulo acc
        go acc ((s,t):rest) = do
           (usable, followUp) <- doOne acc s t
           go (usable `mappend` acc) (followUp `mappend` rest)

        doOne = oo "doOne" doOneO
--        doOneO _ acc s | pprTrace ("doOne" <+> acc <+> s) False = undefined
        doOneO (O o _) acc s =
           evalTerm (iUsableRulesVarM m trs dps s >=> \vacc -> return (Set.map EqModulo vacc, mempty)) $ \in_t -> do
                   t'  <- wrap `liftM` ({-o "icap"-} icap p s `T.mapM` in_t)
                   let rr  = [ EqModulo rule
                                    | rule@(l:->_r) <- rules trs
                                    , not(isVar l)
                                    , unifies l t'
                                    , Just sigma <- [{-o "unify"-} unify l t']
                                    , all ((`inQNF` q) . applySubst sigma) s
                                    , all ((`inQNF` q) . applySubst sigma) (directSubterms l)
                                    ]
                   let new = Set.difference (Set.fromList rr) acc
                   new' <- getFresh (map eqModulo $ F.toList ( o "new" new))
                   let rhsSubterms = [ (directSubterms l,r)
                                       | l :-> r <- new' ]
                   return (new, mconcat [rhsSubterms, map (s,) (F.toList in_t)])

    in do
        tt'  <- {-o "getFresh"-} getFresh tt
        trs' <- go Set.empty $ map (s,) tt'
        return (tRS $ toList trs')


--    trs' <- f_UsableRules (m,trs) (iUsableRulesVarM m trs dps) s =<< getFresh tt
--    return (tRS $ toList trs')

-- instance (Ord(Term t v), Ord v, Rename v, Unify t, HasId t) => IUsableRules t v Rewriting [Rule t v] where
--   iUsableRulesM    = deriveUsableRulesFromTRS (proxy :: Proxy (NarradarTRS t v))
--   iUsableRulesVarM = deriveUsableRulesVarFromTRS (proxy :: Proxy (NarradarTRS t v))

-- instance (Ord(Term t v), Ord v, Rename v, Unify t, HasId t) => IUsableRules t v IRewriting [Rule t v] where
--   iUsableRulesM    = deriveUsableRulesFromTRS (proxy :: Proxy (NarradarTRS t v))
--   iUsableRulesVarM = deriveUsableRulesVarFromTRS (proxy :: Proxy (NarradarTRS t v))

instance (FrameworkTerm t v, Pretty(NarradarTRS t v)
         ) => NeededRules (QRewriting (Term t v)) (NarradarTRS t v) where
   neededRulesM typ trs dps = iUsableRulesM typ trs dps []

-- Insert Pairs

instance FrameworkId id =>InsertDPairs (QRewriting (TermN id)) (NTRS id) where insertDPairs = insertDPairsDefault

-- Hood

--instance Observable t => Observable (QRewriting t) where observer (QRewriting x m) = send ("Q Problem") (return QRewriting << x << m)
instance Observable1 QRewriting
instance (Observable t) => Observable1 (Problem (QRewriting t))
