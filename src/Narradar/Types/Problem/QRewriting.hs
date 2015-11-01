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
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric, DeriveDataTypeable, DeriveAnyClass #-}
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
         , qrewriting, qRewritingO, QSet(..), qmin, qset, qSetO, qSetO'
         , Problem(..)
         , inQNF, isQInnermost
         , qCondition', isQValid, isQConfluent, mkQConditionO
--         , Strategy(..), HasStrategy(..), Standard, Innermost, isInnermost
--         , Minimality(..), HasMinimality(..), getMinimalityFromProblem
         ) where

import Control.Applicative
import Control.Applicative.Compose
import Control.DeepSeq
import Control.DeepSeq.Extras
import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Free.Extras
import Control.Monad.Variant
import Control.Exception (assert)
import Data.Coerce
import Data.Constraint
import Data.Constraint.Forall
import Data.Foldable as F (Foldable(..), toList)
import Data.Functor1
import Data.Graph as G (Graph, buildG, edges)
import Data.Map (Map)
import qualified Data.Map as Map
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

import Data.Term (mapTerm, freshWith')
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
import Narradar.Utils (return2, fmap2, snub, pprTrace, none, Comparable(..), comparableEqO, (<$$>), (<$$$>))

import GHC.Generics (Generic)
import Debug.Hoed.Observe

import Unsafe.Coerce
import System.IO.Unsafe

data QVar = Q Int | V {fromV::Var} deriving (Eq, Ord, Show, Generic, NFData, Observable)
type instance Family.Var QVar = QVar
instance Enum QVar where fromEnum (Q x) = x ; toEnum = Q
instance Pretty QVar where
  pPrint (Q x) = braces(text "q" <+> x)
  pPrint (V x) = pPrint x
instance PprTPDB QVar where pprTPDB (V x) = pprTPDB x
instance Rename QVar where
  rename (V a) (V b) = V $ rename a b
  rename x y = y

-- Note the use of ugly memoization to speed up inQNF calls
-- And the use of disjoing namespaces to prevent variable capture
data QSet t = QSet {terms :: Set(Term t QVar), inQNFmemo :: MVar (Map (Term t QVar) Bool) }
                  deriving ( Generic, Typeable )

qSetIO (O oo o) tt = do
  memo <- newMVar mempty
  return $ QSet (Set.fromList tt) memo

qSetO  o tt = qSetO' o $ fmap2 V tt
qSetO' o tt = unsafePerformIO (qSetIO o tt) 

inQNF_IO :: forall t. (Ord1 t, Match t) => Term t Var -> QSet t -> IO Bool
inQNF_IO t q = do

  table <- readMVar (inQNFmemo q)
  let solve terms t
        | Prelude.any (`matches` t) terms = return False
        | otherwise = allM (loop . canonicalize) (properSubterms t)
      loop (canonicalize -> t) =
        case Map.lookup t table of
          Just x -> return x
          Nothing -> do
            r <- solve (terms q) t
            modifyMVar_ (inQNFmemo q) (return . Map.insert t r)
            return r
  loop (canonicalize t)
  where
      -- inlined implementation of matching
      -- skipping renaming and recursing with the memo table
      allM f [] = return True
      allM f (x:xx) = do
        v <- f x
        if v then allM f xx else return False

      canonicalize :: forall v. (Ord v, Rename v, Observable v) => Term t v -> Term t QVar
      canonicalize = runVariant' freshVars . freshWith' (\_ x -> x)
      freshVars = Q <$> [0..]

inQNF :: (Ord1 t, Match t) => Term t Var -> QSet t -> Bool
inQNF t q = unsafePerformIO (inQNF_IO t q)

mapQSetIO :: (Functor f, Functor g, Ord1 g
           ) => (forall a. f a -> g a) -> QSet f -> IO(QSet g)
mapQSetIO f (QSet tt memoVar) = do
  memo <- readMVar memoVar
  memo' <- newMVar (Map.mapKeysMonotonic (mapTerm f) memo)
  return(QSet (Set.map(mapTerm f) tt) memo')

mapQSet :: (Functor f, Functor g, Ord1 g
           ) => (forall a. f a -> g a) -> QSet f -> QSet g
mapQSet f q = unsafePerformIO $  mapQSetIO f q

instance (Eq1 t) => Eq (QSet t) where q1 == q2 = terms q1 == terms q2
instance Ord1 t => Ord (QSet t) where compare q1 q2 = compare (terms q1) (terms q2)
instance Show1 t => Show (QSet t) where show q = show ("QSet", toList(terms q))

instance (NFData1 term, NFData(Family.Id term)
         ) => NFData (QSet term) where
  rnf (QSet tt m) = rnf1 tt
instance Observable1 t => Observable (QSet t) where
  observer (QSet qset m) = send "QSet" (return (`QSet` m) << qset)
instance (Ord(Family.Id term), HasId1 term, Foldable term
         ) => HasSignature (QSet term) where
  getSignature QSet{terms=q} = getSignature q
instance (Functor term, Pretty(term(Term term Var))) => Pretty (QSet term) where
  pPrint QSet{terms=tt} = "QSet:" <+> fsep (fromV <$$> toList tt)

--instance Ord1 t => GetFresh(QSet t) where getFreshM (QSet tt m) = (`QSet` m) `liftM` getFreshM tt
instance (Functor t, Foldable t) => GetVars (QSet t) where getVars = getVars . terms


type instance Family.TermF (QSet term) = term
type instance Family.Id    (QSet term) = Family.Id term
type instance Family.Var   (QSet term) = QVar

-- | NF(Q) \subseteq NF(R)
mkQConditionO :: (FrameworkT t, Observable (Term t Var)
                ) => Observer -> QSet t -> NarradarTRS t Var -> Bool
mkQConditionO (O o _) q trs = none (`inQNF` q) (lhs <$> rules trs)

-- | NF(R) \subseteq NF(Q)
qCondition' QSet{terms=qset} trs = none (R.isNF trs) (fromV <$$> toList qset)

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

qRewritingO :: ( Functor t, Ord1 t, Observable1 t, Observable (Family.Id t), Observable(Term t Var)
               ) => Observer -> [Term t Var] -> Minimality -> QRewriting t
qRewritingO o tt = lift . QRewriting (qSetO o tt)

qrewriting :: (QRewritingConstraint term) => QRewriting term
qrewriting = lift $ QRewriting (qSetO nilObserver []) M


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

instance (QRewritingConstraint term, Match term
         ) => Eq (EqModulo (QRewriting term)) where
  EqModulo (lower -> QRewriting q m) == EqModulo (lower -> QRewriting q' m') =
    m == m' && EqModulo q == EqModulo q'

instance (Match t, Ord1 t) => Eq(EqModulo (QSet t)) where
  EqModulo a == EqModulo b = EqModulo (terms a) == EqModulo (terms b)

isQInnermost = qCondition
isQValid   (QRewritingProblem trs _ q _ _) = qCondition' q (rules trs)


isQConfluent :: forall t.
                (Unify t, Eq1 t, Observable1 t
                ) => QSet t -> [Rule t Var] -> Bool
isQConfluent = isQConfluentO nilObserver

isQConfluentO :: forall t.
                (Unify t, Observable1 t, Eq1 t
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
  mapRO o f (QRewritingProblem rr p q m _) =
    mkDPProblemO o (lift $ QRewriting q m) (f rr) p

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

  mkDPProblemO obs typ rr dd = QRewritingProblem rr dd' q m qCondition
    where
       p0 = QRewritingProblem rr dd q m qCondition
       ~(QRewriting q m) = lower typ
       qCondition = mkQConditionO obs q rr
       dd' = case lowerNTRS dd of
               pp@DPTRS{typ=typ',rulesUsed} | typ' == Comparable typ
                                       && Set.fromList(rules rr) == rulesUsed
                         -> dd
               otherwise -> getP $ dpTRSO obs p0

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
     , parens (text "STRATEGY Q" <+> fsep (map pprTPDB (toList q)))
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
          if and [ or [ not(inQNF t q)
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
                        _o "s in qnf" (all ((\s -> inQNF s q) . applySubst sigma) s) &&
                        _o "l in qnf" (all ((\s -> inQNF s q) . applySubst sigma) (directSubterms l))
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
  expandDPairO (O o oo) p i new = setP dptrs' p where
    dptrsE = lowerNTRS $ getP $ defExpand
    defExpand = oo "expandDPairDefault" expandDPairOdefault p i new
    dptrs' = dg'' `seq` liftNF (dptrsE{ depGraph = dg'' })
    -- ignore the new graph computed by expandDPairDefault,
    -- using only its bounds in putting together a custom graph
    dg'' = G.buildG bb edges'
    edges' = do
      mn <- edgesdg
      case mn of
        (m,n)
          | m == i && n == i -> [(i+j,i+k) | j <- newIndexes, k <- newIndexes]
          | m == i -> [(i+j,n) | j <- newIndexes]
          | n == i -> [(m,i+j) | j <- newIndexes]
          | otherwise -> return mn

    newIndexes = [0..ln]
    edgesdg = edges dg
    ln  = length (snub new) - 1
    dptrs = lowerNTRS $ getP p
    dg  = depGraph dptrs
--  bb  = G.bounds $ depGraph dptrs
    bb  = o "bb" $ G.bounds $ dpsA dptrsE

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
