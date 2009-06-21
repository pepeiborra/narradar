{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

module Narradar.Types.Problem where

import Control.Applicative
import Control.Exception (assert)
import Control.Monad.List
import Control.Monad.State
import Data.Array as A
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable as F (Foldable(..), toList)
import Data.Graph (Graph, edges, buildG)
import Data.Maybe (isJust)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable as T
import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import Text.PrettyPrint hiding (char, Mode)
import qualified Text.PrettyPrint as Ppr
import Prelude as P hiding (mapM, pi, sum)
import qualified Prelude as P

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.ProblemType
import Narradar.Types.TRS
import Narradar.Utils.Convert
import Narradar.Utils.Ppr
import Narradar.Utils
import Narradar.Types.Term hiding ((!))
import Narradar.Constraints.Unify
import Narradar.Types.Var

import Data.Term.Rules

---------------------------
-- DP Problems
---------------------------
data ProblemF id a = Problem {typ::(ProblemType id), trs::a ,dps :: !a}
     deriving (Eq,Show,Ord)

instance Ord id => HasSignature (Problem id v) id where
  getSignature (Problem _ trs dps) = getSignature trs `mappend` getSignature dps

type Problem  id   v = ProblemG id (TermF id) v
type ProblemG id t v = ProblemF id (NarradarTRSF id t v (Rule t v))

instance (Ord v, Ord id) => Monoid (Problem id v) where
    mempty = Problem Rewriting mempty mempty
    Problem _ t1 dp1 `mappend` Problem typ2 t2 dp2 = Problem typ2 (t1 `mappend` t2) (dp1`mappend`dp2)

instance (Ord id, Ord v) => HasRules (TermF id) v (Problem id v) where
    rules (Problem _ dps trs) = rules dps `mappend` rules trs

instance (Ord v, Ord id) => GetFresh (TermF id) v (Problem id v) where getFreshM = getFreshMdefault
instance (Ord v, Ord id) => GetVars v (Problem id v) where getVars = foldMap getVars

mkProblem :: (Ord id) => ProblemType id -> NarradarTRS id v -> NarradarTRS id v -> Problem id v
mkProblem typ@(getAF -> Just pi) trs dps = let p = Problem (typ `withAF` AF.restrictTo (getAllSymbols p) pi) trs dps in p
mkProblem typ trs dps = Problem typ trs dps

setTyp t' (Problem _ r p) = mkProblem t' r p

mkDPSig (getSignature -> sig@Sig{definedSymbols, arity}) | dd <- toList definedSymbols =
  sig{definedSymbols = definedSymbols `Set.union` Set.mapMonotonic markDPSymbol definedSymbols
     ,arity          = arity `Map.union` Map.fromList [(markDPSymbol f, getArity sig f) | f <- dd]
     }

instance (Convert (TermN id v) (TermN id' v'), Convert id id', Ord id, Ord id', Ord v') =>
          Convert (Problem id v) (Problem id' v') where
  convert p@Problem{typ} = (fmap convert p){typ = fmap convert typ}

instance (Ord id, Ppr id, Ppr v, Ord v) => Ppr (Problem id v) where
    ppr (Problem Prolog{..} _ _) =
            text "Prolog problem." $$
            text "Clauses:" <+> ppr program $$
            text "Goals:" <+> ppr goals

    ppr (Problem typ trs dps) =
            ppr typ <+> text "Problem" $$
            text "TRS:" <+> ppr trs $$
            text "DPS:" <+> ppr dps

type PrologProblem v = Problem String v

mkPrologProblem :: Ord v => [AF_ String] -> Prolog.Program String -> PrologProblem v
mkPrologProblem gg pgm = mkProblem (Prolog gg pgm) mempty mempty

isPrologProblem = isProlog . typ

isFullNarrowingProblem = isFullNarrowing . typ
isBNarrowingProblem    = isBNarrowing . typ
isGNarrowingProblem    = isGNarrowing . typ
isAnyNarrowingProblem  = isAnyNarrowing . typ
isRewritingProblem     = isRewriting . typ
getProblemAF           = getAF . typ

-- -------------
-- AF Problems
-- -------------

class WithAF t id | t -> id where
  withAF :: t -> AF_ id -> t
  stripGoal    :: t -> t

instance (WithAF (ProblemType id) id) => WithAF (Problem id v) id where
  withAF(Problem typ trs dps) goal = Problem (withAF typ goal) trs dps
  stripGoal (Problem typ trs dps)      = Problem (stripGoal  typ)      trs dps

instance WithAF (ProblemType id) id where
  withAF pt@NarrowingModes{}   pi' = pt{pi=pi'}
  withAF pt@BNarrowingModes{}  pi' = pt{pi=pi'}
  withAF pt@GNarrowingModes{}  pi' = pt{pi=pi'}
  withAF pt@LBNarrowingModes{} pi' = pt{pi=pi'}
  withAF Narrowing   pi = narrowingModes0{pi}
  withAF BNarrowing  pi = bnarrowingModes0{pi}
  withAF GNarrowing  pi = gnarrowingModes0{pi}
  withAF LBNarrowing pi = lbnarrowingModes0{pi}
  withAF Rewriting   _  = Rewriting
--  withAF typ _ = error ("withAF - error: " ++ show(ppr typ))
  stripGoal NarrowingModes{}  = Narrowing
  stripGoal BNarrowingModes{} = BNarrowing
  stripGoal GNarrowingModes{} = GNarrowing
  stripGoal LBNarrowingModes{}= LBNarrowing
  stripGoal m = m
--  withAF typ@Prolog{} _ =

instance (Ord id, Ord v) => ApplyAF (Problem id v) id where
    apply pi p@Problem{trs,dps} = p{trs=apply pi trs, dps=apply pi dps}


-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, but it does to make GHC happy (avoid recursive module dependencies)

ren :: (Enum v, Traversable t, MonadFresh v m) => Term t v -> m(Term t v)
ren = foldTermM (\_ -> return `liftM` freshVar) (return . Impure)

-- Use unification instead of just checking if it is a defined symbol
-- This is not the icap defined in Rene Thiemann, as it does not integrate the REN function
icap :: (Ord id, Enum v, Ord v, MonadFresh v m) => Problem id v  -> TermN id v -> m(TermN id v)
icap (Problem typ trs _) t = do
#ifdef DEBUG
  when (not $ Set.null (getVars trs `Set.intersection` getVars t)) $ do
    error "assertion failed (icap)" `const` t `const` trs
#else
  assert (Set.null (getVars trs `Set.intersection` getVars t)) (return ())
#endif
  rr <- {-getFresh-} return (rules trs)
  let go t = if any (unifies (Impure t) . lhs) rr then return `liftM` freshVar else return (Impure t)
      doVar v | isInnermostLike typ = return2 v
              | otherwise           = return `liftM` freshVar
  foldTermM doVar go t

collapsing trs = any (isVar.rhs) (rules trs)

-- ---------------------
-- Usable rules of a TRS
-- ---------------------

-- Assumes Innermost or Constructor Narrowing
-- TODO Extend to work with Q-narrowing to cover more cases
iUsableRulesM :: (Ord id, Ord v, Enum v, MonadFresh v m) =>
                 Problem id v -> Maybe (AF.AF_ id) -> [TermN id v] -> m(Problem id v)
--iUsableRulesM p _ tt | assert (Set.null (getVars p `Set.intersection` getVars tt)) False = undefined
iUsableRulesM p@(Problem typ trs dps) Nothing tt
  | isInnermostLike typ = do
     rr <- go mempty =<< getFresh tt
     return (mkProblem typ (tRS $ toList rr) dps)
 where
  go acc []       = return acc
  go acc (t:rest) = evalTerm (\_ -> go acc rest) f t where
      f in_t = do
         t'  <- wrap `liftM` (icap p `T.mapM` in_t)
         let rr  = [ r | r <- rules trs, lhs r `unifies` t']
             new = Set.difference (Set.fromList rr) acc
         rhsSubterms <- getFresh (rhs <$> F.toList new)
         go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])


iUsableRulesM p@(Problem typ trs dps) (Just pi) tt
  | isInnermostLike typ = do
     rr <- go mempty =<< getFresh (AF.apply pi tt)
     return (mkProblem typ (tRS $ toList rr) dps)
 where
  pi_rules = [(AF.apply pi r, r) | r <- rules trs]
  pi_p     = AF.apply pi p
--go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = return acc
  go acc (t:rest) = evalTerm (\_ -> go acc rest) f t where
     f in_t = do
        t' <- wrap `liftM` (icap pi_p `T.mapM` in_t)
        let rr = Set.fromList
                [r | (pi_r, r) <- pi_rules, t' `unifies` lhs pi_r]
            new = Set.difference rr acc
        rhsSubterms <- getFresh (AF.apply pi . rhs <$> F.toList new)
        go (new `mappend` acc) (mconcat [rhsSubterms, directSubterms t, rest])

iUsableRulesM p _ _ = return p

iUsableRules :: (Ord v, Enum v, Ord id) => Problem id v -> Maybe (AF.AF_ id) -> [TermN id v] -> Problem id v
iUsableRules p mb_pi tt = (runIcap p . iUsableRulesM p mb_pi) tt

{-
iUsableRules_correct trs (Just pi) = F.toList . go mempty where
  pi_trs = AF.apply pi trs
  --go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t:rest) = evalTerm (\_ -> go acc rest) f t where
    f t0
      | t@(Impure in_t) <- AF.apply pi t0
      , rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , wrap(runSupply' (icap pi_trs `T.mapM` in_t) ids) `unifies` lhs pi_r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])
  ids = [0..] \\ (concatMap.concatMap) collectVars (rules trs)
-}

-- ------------------------------------
-- Dealing with the pairs in a problem
-- ------------------------------------

-- | Assumes that the rules have already been renamed apart
dpTRS :: (Ord id, id ~ Identifier a) => Problem id Var -> Graph -> NarradarTRS id Var
dpTRS p edges = DPTRS dps_a edges unifs (getSignature the_dps)
    where dps_a   = listArray (0, length the_dps - 1) the_dps
          unifs   = runIcap p (computeDPUnifiers p)
          the_dps = rules (dps p)

dpTRS' dps edges unifiers = DPTRS dps edges unifiers (getSignature $ elems dps)

expandDPair :: (Ord a, Ppr id, id ~ Identifier a, t ~ TermF id, v ~ Var) =>
               Problem id v -> Int -> [DP a v] -> Problem id v
expandDPair p@Problem{dps=DPTRS dps gr (unif :!: unifInv) _} i (filter (`notElem` elems dps) . snub -> newdps)
 = assert (isValidUnif res) res
  where
   res = runIcap (rules p ++ newdps) $ do
    let dps'     = tRS (dps1 ++ dps2 ++ newdps)
        l_dps'   = l_dps + l_newdps
        a_dps'   = A.listArray (0,l_dps') (rules dps')
        mkUnif' arr arr' =
            A.array ((0,0), (l_dps', l_dps'))
                       ([((adjust x,adjust y), sigma) | ((x,y), sigma) <- assocs arr
                                                      , x /= i, y /= i] ++
                        concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
                                 | j <- new_nodes, k <- [0..l_dps']
                                 , let in1 = (j,k), let in2 = (k,j)])
        gr'      = buildG (0, l_dps')
                   ([(adjust x,adjust y) | (x,y) <- edges gr, x/=i, y/=i] ++
                    [(n,n') | n' <- new_nodes
                            , (n,m) <- edges gr, n/=i, m == i ] ++
                    [(n',n) | n <- gr ! i, n' <- new_nodes] ++
                    [(n',n'') | n' <- new_nodes, n'' <- new_nodes, i `elem` gr ! i])
        adjust x = if x < i then x else x-1

    unif_new :!: unifInv_new <- computeDPUnifiers p{dps = dps'}
    let unif'    = mkUnif' unif    unif_new
        unifInv' = mkUnif' unifInv unifInv_new
        dptrs'   = dpTRS' a_dps' gr' (unif' :!: unifInv')
    return p{dps=dptrs'}

   (dps1,_:dps2) = splitAt i (elems dps)
   new_nodes= [l_dps .. l_dps + l_newdps]
   l_dps    = assert (fst (bounds dps) == 0) $ snd (bounds dps)
   l_newdps = length newdps - 1

expandDPair (Problem typ trs dps) i newdps = mkProblem typ trs (tRS dps')
  where
    dps'          = dps1 ++ dps2 ++ newdps
    (dps1,_:dps2) = splitAt i (rules dps)


computeDPUnifiers :: (Enum v, Ord v, Ord id, MonadFresh v m, unif ~ Unifiers (TermF id) v) =>
                     Problem id v -> m(unif :!: unif)
--computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers p@Problem{typ, dps = (rules -> the_dps)} = do
   p_f <- getFresh p
   let mbUsableRules x = if (isBNarrowing .|. isGNarrowing) typ
                               then  rules $ trs $ iUsableRules p_f Nothing [x]
                               else (rules $ trs p_f)
       u_rr = listArray (0,ldps) $ map (mbUsableRules . rhs) the_dps

   rhss'<- P.mapM (\(_:->r) -> getFresh r >>= icap p) the_dps
   unif <- runListT $ do
                (x, r')      <- liftL $ zip [0..] rhss'
                (y, l :-> _) <- liftL $ zip [0..] the_dps
                let unifier = unify l r'
                return ((x,y), unifier)
   unifInv <- runListT $ do
                (x, _ :-> r) <- liftL $ zip [0..] the_dps
                (y, l :-> _) <- liftL $ zip [0..] the_dps
                let p_inv = p{typ=Rewriting, trs=tRS (swapRule `map` (u_rr ! x))}
                l' <- lift (getFresh l >>= icap p_inv)
                let unifier = unify l' r
                return ((x,y), unifier)
   return(   array ( (0,0), (ldps,ldps) ) unif
         :!: array ( (0,0), (ldps,ldps) ) unifInv)
 where
   liftL = ListT . return
   ldps  = length the_dps - 1

-- -------------
-- Utils
-- -------------

runIcap :: Enum v => GetVars v thing => thing -> State (Substitution t (Either v v), [v]) a -> a
runIcap t m = evalState m (mempty, freshVars) where
    freshVars = map toEnum [1+maximum (0 : map fromEnum (Set.toList $ getVars t)).. ]

-- -------------
-- Sanity Checks
-- -------------

isValidUnif p@(Problem _ _ (DPTRS dps _ (unif :!: _) _)) =
    and $ runIcap p $ runListT $ do
         (x, _ :-> r) <- liftL $ A.assocs dps
         (y, l :-> _) <- liftL $ A.assocs dps
         r' <- getFresh r >>= icap p
         return (unifies l r' == isJust (unif A.! (x,y)))
  where
    liftL = ListT . return

isValidUnif _ = True

-- ------------------
-- Functor Instances
-- ------------------

$(derive makeFunctor     ''ProblemF)
$(derive makeFoldable    ''ProblemF)
$(derive makeTraversable ''ProblemF)
