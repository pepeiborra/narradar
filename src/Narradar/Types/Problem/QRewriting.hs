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
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.QRewriting
         ( QRewriting(..), QRewritingN, qrewriting, QSet(..)
         , Problem(..)
         , inQNF, isQInnermost
         , qCondition, qCondition', isQValid, isQConfluent, mkQCondition
--         , Strategy(..), HasStrategy(..), Standard, Innermost, isInnermost
--         , Minimality(..), HasMinimality(..), getMinimalityFromProblem
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
import qualified Data.Rule.Family as Family
import qualified Data.Term.Family as Family
import Data.Term.Rewriting (isNF, rewrites)
import Data.Typeable
import Text.XHtml (HTML(..), theclass)

import Data.Term.Rules
import qualified Data.Term.Family as Family

import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Types.ArgumentFiltering (ApplyAF)
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.PrologIdentifiers (RemovePrologId)
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils (return2, snub, pprTrace, none, Comparable(..), comparableEqO)
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr

import GHC.Generics (Generic)
import Debug.Hoed.Observe

newtype QSet term = QSet {qset :: [term]}
                  deriving ( Eq, Ord, Show, Functor, Foldable, Traversable
                           , Generic, Typeable, GetMatcher, GetVars)

instance NFData term => NFData (QSet term) where rnf (QSet tt) = rnf tt
instance Observable1 QSet
instance (HasSignature [term], Ord(Family.Id term)) => HasSignature (QSet term) where getSignature (QSet q) = getSignature q
instance Pretty term => Pretty (QSet term) where pPrint (QSet tt) = "QSet:" <+> fsep tt

instance GetFresh t => GetFresh(QSet t) where getFreshM (QSet tt) = QSet `liftM` getFreshM tt

type instance Family.TermF (QSet term) = Family.TermF term
type instance Family.Id    (QSet term) = Family.Id    term
type instance Family.Var   (QSet term) = Family.Var   term

-- | NF(Q) \subseteq NF(R)
mkQCondition :: (FrameworkTerm (Family.TermF trs) (Family.Var trs), Pretty trs
                ,Family.Rule trs ~ RuleFor trs
                ,HasRules trs
                ) => QSet (TermFor trs) -> trs -> Bool
mkQCondition (QSet qt) trs = none (isNF [ q :-> q | q <- qt]) (lhs <$> rules trs)

-- | NF(R) \subseteq NF(Q)
qCondition' (QSet qt) trs = none (isNF trs) qt

inQNF :: ( Ord v, Enum v, Rename v, Observable(Term t v)
         , Unify t) =>
         Term t v -> QSet (Term t v) -> Bool
{-# SPECIALIZE inQNF ::  TermN String -> QSet(TermN String) -> Bool #-}
{-# SPECIALIZE inQNF ::  TermN Id -> QSet(TermN Id) -> Bool #-}
inQNF t (QSet qt) = isNF [ q :-> q | q <- qt] t

data QRewriting term = QRewriting (QSet term) Minimality deriving (Eq, Ord, Show, Functor, Generic, Typeable)

type QRewritingN id = QRewriting (TermN id)

qrewriting = QRewriting (QSet []) M

instance NFData term => NFData (QRewriting term) where rnf (QRewriting q m) = rnf q `seq` rnf m

instance GetPairs (QRewriting term) where getPairs = getPairsDefault

instance IsProblem (QRewriting id) where
  data Problem (QRewriting term) a = QRewritingProblem {rr,dd :: a, q ::QSet term, m :: Minimality, qCondition :: Bool }
                                 deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
  getFramework (QRewritingProblem _ _ q m _) = QRewriting q m
  getR (QRewritingProblem r _ _ _ _) = r

instance (GetFresh term, GetMatcher term, GetVars term
         ,v ~ Family.Var term, Enum v, Ord v, Rename v
         ,Traversable(Family.TermF term)
         ) => Eq (EqModulo (QRewriting term)) where
  EqModulo (QRewriting q m) == EqModulo (QRewriting q' m') =
    m == m' && EqModulo q == EqModulo q'

isQInnermost = qCondition
isQValid   (QRewritingProblem trs _ q _ _) = qCondition' q (rules trs)


isQConfluent :: forall t v.
                (Rename v, Unify t, Ord v, Enum v, Eq (Term t v)
                , Observable(Term t v), Observable v
                ) => QSet (Term t v) -> [RuleF (Term t v)] -> Bool
isQConfluent = isQConfluentO nilObserver

isQConfluentO :: forall t v.
                (Rename v, Unify t, Ord v, Enum v, Eq (Term t v)
                , Observable(Term t v), Observable v
                ) => Observer -> QSet (Term t v) -> [RuleF (Term t v)] -> Bool
isQConfluentO (O o oo) (QSet q) rr = null $ do
  r1 <- rr
  r2 <- rr'
  oo "go" go r1 r2
 where
  go :: Observer -> Rule t v -> Rule t v -> [()]
  go (O o oo) (l1:->r1) (l2:->r2) = do
    Just sigma <- o "sigma" [unify l1 l2]
    guard (o "r1'" (applySubst sigma r1) /= o "r2'" (applySubst sigma r2))
    return ()

  rr' = getVariant rr rr

instance IsDPProblem (QRewriting id) where
  getP   (QRewritingProblem _ p _ _ _) = p

instance (MkDPProblem (QRewriting term) trs
         ,term ~ TermFor trs
         ,Family.Rule trs ~ RuleFor trs
         ,HasRules trs, Monoid trs, Pretty trs
         ,FrameworkTerm (Family.TermF trs) (Family.Var trs)
         ) => MkProblem (QRewriting term) trs where
  mkProblem (QRewriting q m) rr = QRewritingProblem rr mempty q m (mkQCondition q rr)
  mapRO o f (QRewritingProblem rr p q m _) = -- mkDPProblemO o (QRewriting q m) (f r) p
    let rr' = f rr in QRewritingProblem rr' p q m (mkQCondition q rr')

instance (HasSignature trs, HasSignature [term], Family.Id term ~ Family.Id trs) => HasSignature (Problem (QRewriting term) trs) where
  getSignature (QRewritingProblem r p q _ _)  = getSignature r `mappend` getSignature p `mappend` getSignature q

instance (FrameworkId id, Pretty(NTRS id)) =>
  MkDPProblem (QRewriting (TermN id)) (NTRS id)
 where
--  mkDPProblem it@(QRewriting s m) rr dd | pprTrace (text "mkDPProblem rewriting with rules" $$ nest 2 rr) False = undefined
  mkDPProblemO obs@(O o oo) it@(QRewriting q m) rr dd
    = case lowerNTRS dd of
        pp@DPTRS{typ,rulesUsed} | (typ == Comparable it) &&
                                  (Set.fromList(rules rr) == rulesUsed)
                  -> QRewritingProblem rr dd q m (mkQCondition q rr)
        otherwise ->
          dpTRSO obs (\rr p -> p{rr}) (\dd p -> p{dd})
            (QRewritingProblem rr dd q m (mkQCondition q rr))

  mapPO (O o oo) f me@QRewritingProblem{rr,dd,q,m}
    | dd' <- f dd
    = case lowerNTRS dd' of
        DPTRS{typ,rulesUsed}
          |    oo "same problem type" (\(O o oo) ->
                 let new = o "new" $ QRewriting q m
                 in  o "old" typ == Comparable new)
            && o "same rules used"   (Set.fromList(rules rr) == rulesUsed)
            -> me{dd=dd'}
        _ -> oo "dpTRS" dpTRSO (\rr p -> p{rr}) (\dd p -> p{dd}) me{dd=dd'}

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
         , Functor t, Foldable t, HasId1 t, Pretty (Family.Id t)
         ) => PprTPDB (Problem (QRewriting (Term t v)) trs) where
  pprTPDB prob@(QRewritingProblem r p (QSet q) m _) = vcat
     [parens( text "VAR" <+> (fsep $ snub $ map pprTPDB $ toList $ getVars prob))
     ,parens( text "RULES" $$
              nest 1 (vcat $ map pprTPDB $ rules $ r))
     ,if not (null $ rules p)
         then parens( text "PAIRS" $$
              nest 1 (vcat $ map pprTPDB $ rules $ p))
         else Ppr.empty
     , parens (text "STRATEGY Q" <+> fsep (map pprTPDB q))
     ,if m == M then parens (text "MINIMALITY") else Ppr.empty
     ]

-- ICap
instance FrameworkTerm t v => ICap (Problem(QRewriting (Term t v)) (NarradarTRS t v)) where
--  icap (_,rules -> []) s t = return t
  icapO (O o oo) (QRewritingProblem r p q m qC) s t = do
#ifdef DEBUG
    when (not $ Set.null (getVars r `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` p
#else
    assert (Set.null (getVars r `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules r)
    let goO (O o oo) t =
          if and [ or [ not(o "inQNF" inQNF t q)
                              | t <- map (applySubst sigma) s ++
                                     directSubterms (applySubst sigma l)]
                  | l :-> r <- rr
                  , Just sigma <- [o "unify" unify (wrap t) l] ]
                   then return (wrap t) else return `liftM` freshVar
        doVar v = if qC && return v `elem` (concatMap subterms s)
                    then return2 v 
                    else return `liftM` renaming v
    foldTermM doVar (oo "go" goO) t

-- Usable Rules
instance (FrameworkId id, Pretty(NTRS id)
         ) => IUsableRules (Problem (QRewriting (TermN id)) (NTRS id)) where
  iUsableRulesVarMO (O o oo) p@QRewritingProblem{qCondition,rr} _s _
    | o "qCondition" qCondition = return (setR mempty p)
    | otherwise  = return (setR rr p)
  iUsableRulesMO (O _ oo) p@QRewritingProblem{q,rr} s tt =
--    pprTrace ("Q-Usable Rules" <+> tt) $
    let go acc [] = return $ setR (tRS $ map eqModulo $ F.toList acc) p
        go acc ((s,t):rest) = do
           (usable, followUp) <- oo "doOne" doOneO acc s t
           go (usable `mappend` acc) (followUp `mappend` rest)

        doOneO (O o oo) acc s =
           evalTerm (oo "iUsableRulesVarMO" iUsableRulesVarMO p s >=> \p' ->
                       let vacc = Set.fromList $ map EqModulo $ rules $ getR p'
                       in return (vacc, mempty)
                     ) $ \in_t -> do
                   t'  <- wrap `liftM` (oo "icap" icapO p s `T.mapM` in_t)
                   let checkSigma (O o oo) sigma l =
                        o "s in qnf" (all ((\s -> o "inQNF" inQNF s q) . applySubst sigma) s) &&
                        o "l in qnf" (all ((`inQNF` q) . applySubst sigma) (directSubterms l))
                   let  rr'  = o "rr'"
                                 [ EqModulo rule
                                    | rule@(l:->_r) <- rules rr
                                    , not(isVar l)
                                    , Just sigma <- [o "unify" unify l t']
                                    , oo "checkSigma" checkSigma sigma l
                                    ]
                   let  new = o "new" $ Set.difference (Set.fromList rr') acc
                   new' <- getFresh (map eqModulo $ F.toList $ new)
                   let rhsSubterms = [ (directSubterms l, r) | l :-> r <- new' ]
                   return (new, mconcat [rhsSubterms, map (s,) (F.toList in_t)])

    in do
        tt'  <- {-o "getFresh"-} getFresh tt
        p' <- go Set.empty $ map (s,) tt'
        return p'


--    trs' <- f_UsableRules (m,trs) (iUsableRulesVarM m trs dps) s =<< getFresh tt
--    return (tRS $ toList trs')

-- instance (Ord(Term t v), Ord v, Rename v, Unify t, HasId t) => IUsableRules t v Rewriting [Rule t v] where
--   iUsableRulesM    = deriveUsableRulesFromTRS (proxy :: Proxy (NarradarTRS t v))
--   iUsableRulesVarM = deriveUsableRulesVarFromTRS (proxy :: Proxy (NarradarTRS t v))

-- instance (Ord(Term t v), Ord v, Rename v, Unify t, HasId t) => IUsableRules t v IRewriting [Rule t v] where
--   iUsableRulesM    = deriveUsableRulesFromTRS (proxy :: Proxy (NarradarTRS t v))
--   iUsableRulesVarM = deriveUsableRulesVarFromTRS (proxy :: Proxy (NarradarTRS t v))

instance (FrameworkId id, Pretty(NTRS id)
         ) => NeededRules (Problem (QRewriting (TermN id)) (NTRS id)) where
   neededRulesM p = iUsableRulesM p []

-- Insert Pairs

instance FrameworkId id => InsertDPairs (QRewriting (TermN id)) (NTRS id) where
  insertDPairsO = insertDPairsDefault

--  Custom Expand Pair instance with the pair-graph expansion of Thiemann
instance FrameworkProblem (QRewriting (TermN id)) (NTRS id) =>
         ExpandDPair (QRewriting (TermN id)) (NTRS id) where
  expandDPairO o p i new = setP (liftNF $ dptrs{ depGraph = dg'' }) p where
    dptrs = lowerNTRS $ getP $ expandDPairOdefault o p i new
    -- ignore the new graph computed by expandDPairDefault,
    -- using only its bounds in putting together a custom graph
    dg'' = G.buildG bb $
           [ (m,i+j)   | (m,n) <- edges dg, n == i, j <- [0..length new - 1] ] ++
           [ (i+j,n)   | (m,n) <- edges dg, m == i, j <- [0..length new - 1] ] ++
           [ (i+j,i+k) | (m,n) <- edges dg, m == i, n == i
                       , j <- [0..length new - 1]
                       , k <- [0..length new - 1]] ++
          edges dg

    dg  = depGraph (lowerNTRS $ getP p)
--  bb  = G.bounds $ depGraph dptrs
    bb  = G.bounds $ dpsA dptrs
-- Hood

--instance Observable t => Observable (QRewriting t) where observer (QRewriting x m) = send ("Q Problem") (return QRewriting << x << m)
instance Observable1 QRewriting
instance (Observable t) => Observable1 (Problem (QRewriting t))
