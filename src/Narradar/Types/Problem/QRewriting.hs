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
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem.QRewriting
         ( QRewriting(..), QRewritingN, QRewritingConstraint
         , qrewriting, qRewritingO, QSet(..), qmin, qset
         , Problem(..)
         , inQNF, inQNFo, isQInnermost
         , qCondition', isQValid, isQConfluent, mkQConditionO
--         , Strategy(..), HasStrategy(..), Standard, Innermost, isInnermost
--         , Minimality(..), HasMinimality(..), getMinimalityFromProblem
         ) where

import Control.Applicative
import Control.Applicative.Compose
import Control.DeepSeq
import Control.DeepSeq.Extras
import Control.Monad
import Control.Exception (assert)
import Data.Coerce
import Data.Constraint
import Data.Constraint.Forall
import Data.Foldable as F (Foldable(..), toList)
import Data.Functor1
import Data.Graph as G (Graph, buildG, edges)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(..))
import Data.Traversable as T (Traversable(..), mapM)
import Data.Set (Set)
import qualified Data.Array as G
import qualified Data.Set as Set
import qualified Data.Rule.Family as Family
import qualified Data.Term.Family as Family
import Data.Typeable
import Text.XHtml (HTML(..), theclass)
import Prelude.Extras

import Data.Term (mapTerm)
import Data.Term.Rules
import Data.Term.Automata hiding (map)
import qualified Data.Term.Automata as Automata
import qualified Data.Term.Family as Family
import qualified Data.Term.Rewriting as R

import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Framework.Constraints
import Narradar.Types.ArgumentFiltering (ApplyAF)
import Narradar.Types.DPIdentifiers
import Narradar.Types.Problem
import Narradar.Types.PrologIdentifiers (RemovePrologId)
import Narradar.Types.TRS
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils (return2, snub, pprTrace, none, Comparable(..), comparableEqO)

import GHC.Generics (Generic)
import Debug.Hoed.Observe

import Unsafe.Coerce

data QSet t = QSet {terms :: [Term t Var], matcher :: TermMatcher t Var }
                  deriving ( Generic, Typeable)

qSetO o tt = QSet tt (createMatcherO o tt)

mapQSet :: (Functor f, Functor g, Ord1 g
           ) => (forall a. f a -> g a) -> QSet f -> QSet g
mapQSet f (QSet tt matcher) = QSet (mapTerm f <$> tt) (Automata.map f matcher)
{-
instance (Eq(Family.Id term), Eq1 term) => Eq (QSet term) where
  QSet t1 m1 == QSet t2 m2 = eq \\ (inst :: Forall Eq1 \\ inst where
    eq :: ( Eq(term(Term term Var))
          , Eq(term(TermMatcher term))
          ) => Bool
    eq = t1 == t2 && m1 == m2
-}

deriving instance (Eq1 t) => Eq (QSet t)
deriving instance (Ord1 term) => Ord (QSet term)
deriving instance (Show1 term) => Show (QSet term)

instance (Applicative t, Traversable t, Eq1 t) => GetMatcher (QSet t) where getMatcherM a b = getMatcherM (terms a) (terms b)

instance (NFData1 term, NFData(Family.Id term)
         ) => NFData (QSet term) where
  rnf (QSet tt m) = rnf1 tt `seq` rnf m
instance Observable1 t => Observable (QSet t) where
  observer (QSet qset m) = send "QSet" (return (`QSet` m) << qset)
instance (Ord(Family.Id term), HasId1 term, Foldable term
         ) => HasSignature (QSet term) where
  getSignature QSet{terms=q} = getSignature q
instance (Pretty(term(Term term Var))) => Pretty (QSet term) where
  pPrint QSet{terms=tt} = "QSet:" <+> fsep tt

instance GetFresh(QSet t) where getFreshM (QSet tt m) = (`QSet` m) `liftM` getFreshM tt
instance (Functor t, Foldable t) => GetVars (QSet t) where getVars = getVars . terms


type instance Family.TermF (QSet term) = term
type instance Family.Id    (QSet term) = Family.Id term
type instance Family.Var   (QSet term) = Var

-- | NF(Q) \subseteq NF(R)
mkQConditionO :: (FrameworkT t, Observable (Term t Var)
                ) => Observer -> QSet t -> NarradarTRS t Var -> Bool
mkQConditionO (O o _) QSet{..} trs =
--  none (o "isNF" isNF matcher) (lhs <$> rules trs)
  none (R.isNF [ q :-> q | q <- terms]) (lhs <$> rules trs)

-- | NF(R) \subseteq NF(Q)
qCondition' QSet{terms=qset} trs = none (R.isNF trs) qset


inQNF :: ( FastMatch t Var
         , Applicative (Maybe :+: t)
         , Pretty (Term t Var), Observable(Term t Var)
         ) =>
         Term t Var -> QSet t -> Bool
inQNF = inQNFo nilObserver

inQNFo :: ( FastMatch t Var
         , Applicative (Maybe :+: t)
         , Pretty (Term t Var), Observable(Term t Var)
         ) =>
         Observer -> Term t Var -> QSet t -> Bool
{-# SPECIALIZE inQNFo ::  Observer -> TermN String -> QSet(TermF String) -> Bool #-}
{-# SPECIALIZE inQNFo ::  Observer -> TermN Id -> QSet(TermF Id) -> Bool #-}
inQNFo (O o oo) t QSet{terms, matcher} = res' -- if (res == res') then res else err
 where
  err  =
    error $ show $
    if res && not res' then
      let Just (p,t') = force $ oo "rewrite1" R.rewrite1O' [t :-> t | t <- terms] t in
      (text "Tree matcher claims" <+> t <+> text "is a normal form but there is a reduct at position" <+> p <+> text "and it reduces to" <+> t' <> colon $$ vcat terms)
     else
      (text "Tree matcher claims" <+> t <+> text "is not a normal form but Rewriting disagrees:" $$ vcat terms)
  res  =   isNF matcher t
  res' = R.isNF [ t :-> t | t <- terms] t

data QRewriting_ t = QRewriting {qset_ :: QSet t, qmin_ :: Minimality} deriving (Generic, Typeable)

class (Functor f, Observable1 f, Ord1 f) => QRewritingConstraint f
instance (Functor f, Observable1 f, Ord1 f) => QRewritingConstraint f
deriving instance Typeable QRewritingConstraint

type QRewriting = NF1 QRewritingConstraint QRewriting_
type QRewritingN id = QRewriting (TermF id)

lift :: QRewritingConstraint t => QRewriting_ t -> QRewriting t
lift  = liftNF1
lower :: forall g. QRewritingConstraint g => QRewriting g -> QRewriting_ g
lower = lowerNF1 fmapQRewriting where
  fmapQRewriting :: forall f. QRewritingConstraint f =>
                    (forall a. f a -> g a) -> QRewriting_ f -> QRewriting_ g
  fmapQRewriting f (QRewriting qset qmin) =
    QRewriting (mapQSet f qset) qmin

qmin x = qmin_ . lower $ x
qset x = qset_ . lower $ x

qRewritingO :: ( Observable1 t, Observable (Family.Id t), Observable(Term t Var)
               , FastMatch t Var
               ) => Observer -> [Term t Var] -> Minimality -> QRewriting t
qRewritingO o tt = lift . QRewriting (qSetO o tt)

qrewriting :: (QRewritingConstraint term, FastMatch term Var) => QRewriting term
qrewriting = lift $ QRewriting (QSet [] mempty) M


deriving instance (Eq1 term) => Eq (QRewriting_ term)
deriving instance (Ord1 term) => Ord (QRewriting_ term)
deriving instance (Show1 term) => Show (QRewriting_ term)

instance (QRewritingConstraint term) => Eq(QRewriting term) where a == b = lower a == lower b
instance (QRewritingConstraint term) => Ord(QRewriting term) where compare a b = compare (lower a) (lower b)
instance (Show1 term, QRewritingConstraint term) => Show(QRewriting term) where show = show . lower

instance ( QRewritingConstraint term, NFData(Family.Id term), NFData1 term
         ) => NFData (QRewriting term) where
  rnf (lower -> QRewriting q m) = rnf q `seq` rnf m

instance GetPairs (QRewriting term) where getPairs = getPairsDefault

instance QRewritingConstraint t => IsProblem (QRewriting t) where
  data Problem (QRewriting term) a = QRewritingProblem {rr,dd :: a, q ::QSet term, m :: Minimality, qCondition :: Bool }
                                 deriving (Functor, Foldable, Traversable, Generic)
  getFramework (QRewritingProblem _ _ q m _) = lift $ QRewriting q m
  getR (QRewritingProblem r _ _ _ _) = r

deriving instance (Eq trs, Eq1 term, Eq(Family.Id term)) => Eq (Problem (QRewriting term) trs)
deriving instance (Ord trs, Ord1 term, Ord(Family.Id term)) => Ord (Problem (QRewriting term) trs)
deriving instance (Show trs, Show1 term, Show(Family.Id term)) => Show (Problem (QRewriting term) trs)

instance (QRewritingConstraint term, FastMatch term Var
         ,Match term
         ) => Eq (EqModulo (QRewriting term)) where
  EqModulo (lower -> QRewriting q m) == EqModulo (lower -> QRewriting q' m') =
    m == m' && EqModulo q == EqModulo q'

instance (Traversable t, Match t) => Eq(EqModulo (QSet t)) where
  EqModulo a == EqModulo b = EqModulo (terms a) == EqModulo (terms b)

isQInnermost = qCondition
isQValid   (QRewritingProblem trs _ q _ _) = qCondition' q (rules trs)


isQConfluent :: forall t.
                (Unify t, Eq1 t, Observable(Term t Var)
                ) => QSet t -> [Rule t Var] -> Bool
isQConfluent = isQConfluentO nilObserver

isQConfluentO :: forall t.
                (Unify t, Observable (Term t Var), Eq1 t
                ) => Observer -> QSet t -> [Rule t Var] -> Bool
isQConfluentO (O o oo) QSet{terms=q} rr = null $ do
  r1 <- rr
  r2 <- rr'
  oo "go" go r1 r2
 where
--  go :: Observer -> Rule t v -> Rule t v -> [()]
  go (O o oo) (l1:->r1) (l2:->r2) = do
    Just sigma <- o "sigma" [unify l1 l2]
    guard (o "r1'" (applySubst sigma r1) /= o "r2'" (applySubst sigma r2))
    return ()

  rr' = getVariant rr rr

instance QRewritingConstraint term => IsDPProblem (QRewriting term) where
  getP   (QRewritingProblem _ p _ _ _) = p

instance (FrameworkTerm term Var
         ) => MkProblem (QRewriting term) (NarradarTRS term Var) where
  mkProblemO o (lower -> QRewriting q m) rr =
    QRewritingProblem rr mempty q m (mkQConditionO o q rr)
  mapRO o f (QRewritingProblem rr p q m _) = -- mkDPProblemO o (QRewriting q m) (f r) p
    let rr' = f rr in QRewritingProblem rr' p q m (mkQConditionO o q rr')
  setR_uncheckedO _ rr p = p{rr}

instance ( HasSignature trs, HasId1 term, Foldable term
         , Family.Id trs ~ Family.Id term
         ) => HasSignature (Problem (QRewriting term) trs) where
  getSignature (QRewritingProblem r p q _ _)  = getSignature r `mappend` getSignature p `mappend` getSignature q

instance ( FrameworkTerm t Var, Pretty(NarradarTRS t Var)
         ) =>
  MkDPProblem (QRewriting t) (NarradarTRS t Var)
 where
--  mkDPProblem it@(QRewriting s m) rr dd | pprTrace (text "mkDPProblem rewriting with rules" $$ nest 2 rr) False = undefined
  mkDPProblemO obs@(O o oo) it@(lower -> QRewriting q m) rr dd
    = case lowerNTRS dd of
        pp@DPTRS{typ,rulesUsed} | (typ == Comparable it) &&
                                  (Set.fromList(rules rr) == rulesUsed)
                  -> QRewritingProblem rr dd q m (mkQConditionO obs q rr)
        otherwise ->
          dpTRSO obs
            (QRewritingProblem rr dd q m (mkQConditionO obs q rr))

  mapPO (O o oo) f me@QRewritingProblem{rr,dd,q,m}
    | dd' <- f dd
    = case lowerNTRS dd' of
        DPTRS{typ,rulesUsed}
          |    oo "same problem type" (\(O o oo) ->
                 let new = o "new" $ lift $ QRewriting q m
                 in  o "old" typ == Comparable new)
            && o "same rules used"   (Set.fromList(rules rr) == rulesUsed)
            -> me{dd=dd'}
        _ -> oo "dpTRS" dpTRSO me{dd=dd'}
  setP_uncheckedO _ dd p = p{dd}

-- Prelude

instance (NFData trs, NFData1 t, NFData(Family.Id t)
         ) => NFData (Problem (QRewriting t) trs) where
  rnf (QRewritingProblem rr dd s m qC) = rnf rr `seq` rnf dd `seq` rnf s `seq` rnf m `seq` rnf qC `seq` ()

-- Framework

instance QRewritingConstraint st => HasMinimality (QRewriting st) where
    getMinimality    (lower -> QRewriting st m) = m
    setMinimality m' (QRewritingProblem rr dd s _ qC) = QRewritingProblem rr dd s m' qC

-- Functor


-- Output

instance QRewritingConstraint term => Pretty (QRewriting term) where
    pPrint (lower -> QRewriting tt M) = text "Q-Rewriting"
    pPrint (lower -> QRewriting tt A) = text "Q-Rewriting (no minimality)"

instance QRewritingConstraint term => HTML (QRewriting term) where
    toHtml (lower -> QRewriting tt M) = toHtml "Q-Rewriting Problem"
    toHtml (lower -> QRewriting tt A) = toHtml "Q-Rewriting Problem (no minimality)"

instance QRewritingConstraint term => HTMLClass (QRewriting term) where
  htmlClass (lower -> QRewriting tt m) = theclass "QDP"


instance (HasRules trs, GetVars trs, Pretty v, PprTPDB v, Pretty (t(Term t v)), Ord v
         , Family.Rule trs ~ Rule t v
         , Family.Var  trs ~ v
         , Functor t, Foldable t, HasId1 t, Pretty (Family.Id t)
         ) => PprTPDB (Problem (QRewriting t) trs) where
  pprTPDB prob@(QRewritingProblem r p (QSet{terms=q}) m _) = vcat
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
instance FrameworkTerm t Var => ICap (Problem(QRewriting t) (NarradarTRS t Var)) where
--  icap (_,rules -> []) s t = return t
  icapO o@(O _o oo) (QRewritingProblem r p q m qC) s t = do
#ifdef DEBUG
    when (not $ Set.null (getVars r `Set.intersection` getVars t)) $ do
      error "assertion failed (icap)" `const` t `const` p
#else
    assert (Set.null (getVars r `Set.intersection` getVars t)) (return ())
#endif
    rr <- {-getFresh-} return (rules r)
    let goO (O o oo) t =
          if and [ or [ not(oo "inQNF" inQNFo t q)
                              | t <- map (applySubst sigma) s ++
                                     directSubterms (applySubst sigma l)]
                  | l :-> r <- rr
                  , Just sigma <- [{- o "unify" -} unify (wrap t) l] ]
                   then return (wrap t) else return `liftM` freshVar
        doVar v = if qC && return v `elem` (concatMap subterms s)
                    then return2 v 
                    else return `liftM` renaming v
    foldTermM doVar ({-oo "go" -} goO o) t

-- Usable Rules
instance ( FrameworkTerm t Var
         ) => IUsableRules (Problem (QRewriting t) (NarradarTRS t Var)) where
  iUsableRulesVarMO o@(O _o oo) p@QRewritingProblem{qCondition,rr} _s _
    | {-o "qCondition"-} qCondition = return (setR mempty p)
    | otherwise  = return (setR rr p)
  iUsableRulesMO o@(O _ oo) p@QRewritingProblem{q,rr} s tt =
--    pprTrace ("Q-Usable Rules" <+> tt) $
    let go acc [] = return $ setR (tRS $ map eqModulo $ F.toList acc) p
        go acc ((s,t):rest) = do
           (usable, followUp) <- {-oo "doOne"-} doOneO o acc s t
           go (usable `mappend` acc) (followUp `mappend` rest)

        doOneO o@(O _o oo) acc s =
           evalTerm ({-oo "iUsableRulesVarMO"-} iUsableRulesVarMO o p s >=> \p' ->
                       let vacc = Set.fromList $ map EqModulo $ rules $ getR p'
                       in return (vacc, mempty)
                     ) $ \in_t -> do
                   t'  <- wrap `liftM` ({-oo "icap"-} icapO o p s `T.mapM` in_t)
                   let checkSigma o@(O _o oo) sigma l =
                        _o "s in qnf" (all ((\s -> oo "inQNF" inQNFo s q) . applySubst sigma) s) &&
                        _o "l in qnf" (all ((\s -> oo "inQNF" inQNFo s q) . applySubst sigma) (directSubterms l))
                   let  rr'  = {- o "rr'" -}
                                 [ EqModulo rule
                                    | rule@(l:->_r) <- rules rr
                                    , not(isVar l)
                                    , Just sigma <- [{- o "unify" -} unify l t']
                                    , {-oo "checkSigma"-} checkSigma o sigma l
                                    ]
                   let  new = {-o "new" $ -} Set.difference (Set.fromList rr') acc
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

instance (FrameworkTerm t Var
         ) => NeededRules (Problem (QRewriting t) (NarradarTRS t Var)) where
   neededRulesM p = iUsableRulesM p []

-- Insert Pairs

instance (FrameworkId id, NFData(TermMatcher (TermF id) Var)
         ) => InsertDPairs (QRewriting (TermF id)) (NarradarTRS (TermF id) Var) where
  insertDPairsO = insertDPairsDefault

--  Custom Expand Pair instance with the pair-graph expansion of Thiemann
instance ( FrameworkTerm t Var
         , InsertDPairs (QRewriting t) (NarradarTRS t Var)
         , Pretty (t(Term t Var))
         ) =>
         ExpandDPair (QRewriting t) (NarradarTRS t Var) where
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
instance Observable1 f => Observable (QRewriting_ f)
instance Observable (QRewriting f) where
  observer (FMap1 f qr) = FMap1 f . observer qr
instance (Observable1 t) => Observable1 (Problem (QRewriting t)) where
  observer1 (QRewritingProblem rr d q m qCond) = send "QRewritingProblem" (return QRewritingProblem << rr << d << q << m << qCond)

instance (Observable a, Observable1 t) => Observable (Problem (QRewriting t) a) where
  observer = observer1
  observers = observers1
