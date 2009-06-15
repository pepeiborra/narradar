{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module Narradar.TRS where

import Control.Applicative
import "control-monad-free" Control.Monad.Free (evalFree, wrap)
import Control.Monad.List
import Control.Monad.State
import Control.Monad.Supply
import Control.Parallel.Strategies
import Data.Array.IArray as A
import Data.Graph (Graph, edges, buildG)
import Data.Foldable as F (Foldable, foldMap, toList, concatMap, sum)
import Data.List ((\\))
import Data.Maybe (catMaybes)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Text.PrettyPrint
import Prelude hiding (concatMap)

--import TRS hiding (Ppr, ppr, unify, unifies, (!))
--import qualified TRS
import Data.Term hiding (unify,unifies, (!))
import Data.Term.Rules
import Data.Term.Ppr

import Narradar.ArgumentFiltering (apply, ApplyAF(..))
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Convert
import Narradar.DPIdentifiers
import Narradar.Labellings
import Narradar.ProblemType
import Narradar.Unify
import Narradar.Utils
import Narradar.Term
import Narradar.Var
import qualified Language.Prolog.Syntax as Prolog

#ifdef HOOD
import Debug.Observe
#endif

-- --------------------
-- TRSs in our setting
-- --------------------

{-
DPTRS contains an additional payload to cache:
1) the graph
2) the unifiers between the pairs computed by the EDG processor.
3) the unifiers computed by the star EDG processor
The unifiers are cached in a matrix (an (rhs,lhs) array) with the following layout
in the case of 2), and the opposite layout in the case of 3)

\ LHS|     |     |
 \   |pair1|pair2|
RHS\ |     |     |
------------------
pair1|_____|_____|
pair2|_____|_____|
.....|     |     |
-}

data NarradarTRS id v where
    TRS       :: (Ord id) => Set (RuleN id v)                                  -> Signature id -> NarradarTRS id v
    PrologTRS :: (Ord id) => Set (String, RuleN id v)                          -> Signature id -> NarradarTRS id v
    DPTRS     :: (Ord id) => Array Int (RuleN id v) -> !Graph -> Unifiers (TermF id) v :!: Unifiers (TermF id) v -> Signature id -> NarradarTRS id v

type Unifiers t v = Array (Int,Int) (Maybe (Substitution t v))

instance (Ord id, Ord v) => GetVars v (NarradarTRS id v) where getVars = getVars . rules

instance (Ord id, Ord v) => Eq (NarradarTRS id v) where trs1 == trs2 = rules trs1 == rules trs2

instance (Ord id, Ord v) => Ord (NarradarTRS id v) where
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _ _) (DPTRS rr2 _ _ _) = compare rr1 rr2
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT

instance (Ord id, Ord v) => HasRules (TermF id) v (NarradarTRS id v) where
  rules(TRS       rr _)     = toList rr
  rules(PrologTRS rr _)     = map snd (toList rr)
  rules(DPTRS     rr _ _ _) = elems rr
instance (Ord id, Ord v) => IsTRS (TermF id) v (NarradarTRS id v) where
  tRS  rr = TRS (Set.fromList rr) (getSignature rr)

instance (Ord id, Ord v) => Size (NarradarTRS id v) where size = F.sum . fmap size . rules

instance (Convert (TermN id v) (TermN id' v'), Ord id, Ord id', Ord v') =>
          Convert (NarradarTRS id v) (NarradarTRS id' v') where
    convert(PrologTRS rr sig) = prologTRS' (Set.mapMonotonic convert rr)
    convert (TRS rr _)        = narradarTRS (map convert$ toList rr)

mkTRS :: (Ord id, Ord v) => [RuleN id v] -> NarradarTRS id v
mkTRS = tRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS :: forall id v. (Ord id, Ord v) => [(String, RuleN id v)] -> NarradarTRS id v
prologTRS rr = prologTRS' (Set.fromList rr)

prologTRS' :: forall id v. (Ord id) => Set(String, RuleN id v) -> NarradarTRS id v
prologTRS' rr = PrologTRS rr (getSignature (snd <$> toList rr))

narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)

dpTRS :: (Ord id, id ~ Identifier a) => ProblemType id -> NarradarTRS id Var -> [DP a Var] -> Graph -> NarradarTRS id Var
dpTRS typ trs dps edges = dpTRS' typ trs dps' edges
  where dps' = listArray (0, length dps - 1) dps -- (refreshRules dps [])

-- | Assumes that the rules have already been renamed apart
dpTRS' :: (Ord id, id ~ Identifier a, v~Var) => ProblemType id -> NarradarTRS id v -> Array Int (DP a v) -> Graph -> NarradarTRS id v
dpTRS' typ trs dps edges = DPTRS dps edges (runIcap (rules trs `mappend` elems dps)
                                                    (computeDPUnifiers typ trs $ elems dps))
                                           (getSignature $ elems dps)

-- | Assumes that the rules have already been renamed apart
dpTRS'' dps edges unifiers = DPTRS dps edges unifiers (getSignature $ elems dps)

refreshRules :: (Traversable t, MonadEnv t (Either Var Var) m, MonadFresh v m, v ~ Var) => [Rule t v] -> m [Rule t v]
refreshRules rr = mapM2 (freshWith leftName) rr where
        leftName (Var n _) (Var _ i) = Var n i

computeDPUnifiers :: ( Enum v, Ord v, Ord (Term t v), Unify t,  ApplyAF trs id, IsTRS t v trs
                     , GetVars v trs, ApplyAF (Term t v) id, MonadFresh v m, unif ~ Unifiers t v) =>
                     ProblemType id -> trs -> [Rule t v] -> m(unif :!: unif)
--computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers typ trs dps = do
   unif <- runListT $ do
                (x, _ :-> r) <- ListT $ return $ zip [0..] dps
                (y, l :-> _) <- ListT $ return $ zip [0..] dps
                r'  <- lift (icap trs r >>= mbren)
                return ((x,y), unify l r')
   unifInv <- runListT $ do
                (x, _ :-> r) <- ListT $ return $ zip [0..] dps
                (y, l :-> _) <- ListT $ return $ zip [0..] dps
                let trs' = tRS (swapRule <$> mbUsableRules [r]) `asTypeOf` trs
                l' <- lift (icap trs' l >>= ren)
                return ((x,y), unify r l')
   return(   array ( (0,0), (length dps -1 , length dps - 1) ) unif
         :!: array ( (0,0), (length dps -1 , length dps - 1) ) unifInv)
 where
   (mbren, mbUsableRules) = if (isBNarrowing .|. isGNarrowing) typ
                              then (getFresh,iUsableRules trs Nothing)
                              else (ren,const (rules trs))

restrictDPTRS :: NarradarTRS t v -> [Int] -> NarradarTRS t v
restrictDPTRS (DPTRS dps gr (unif :!: unifInv) sig) indexes = DPTRS dps' gr' unif' (getSignature $ elems dps')
  where
   newIndexes = Map.fromList (zip indexes [0..])
   nindexes   = length indexes -1
   dps'       = extractIxx dps indexes `asTypeOf` dps
   gr'        = A.amap (catMaybes . map (`Map.lookup` newIndexes)) (extractIxx gr indexes)
   extractIxx arr nodes = A.listArray (0, length nodes - 1) [arr A.! n | n <- nodes]
   unif' = (reindexArray unif :!: reindexArray unifInv)
   reindexArray arr =
           A.array ( (0,0), (nindexes, nindexes) )
                   [ ( (x',y'), sigma) | ((x,y),sigma) <- A.assocs arr
                                       , Just x' <- [Map.lookup x newIndexes]
                                       , Just y' <- [Map.lookup y newIndexes]]

dpUnify    (DPTRS _ _ (unifs :!: _) _) l r = unifs ! (r,l)
dpUnifyInv (DPTRS _ _ (_ :!: unifs) _) l r = unifs ! (r,l)

expandDPair :: (AF.ApplyAF trs id, IsTRS t v trs, GetVars v trs, id ~ Identifier a, t ~ TermF id, v ~ Var) =>
               ProblemType id -> trs -> NarradarTRS id v -> Int -> [DP a v] -> NarradarTRS id v
--expandDPair (Problem typ rules (DPTRS dps gr unif sig)) i newdps | trace ("expandDPair i="++ show i ++ " dps=" ++ show(numElements dps) ++ " newdps=" ++ show (length newdps)) False = undefined
expandDPair typ trs (DPTRS dps gr (unif :!: unifInv) sig) i newdps
 = runIcap (rules trs ++ elems dps ++ newdps) $ do
    dps'  <- ((dps1 ++ dps2) ++) `liftM` refreshRules newdps
    let a_dps'   = A.listArray (0,length dps' - 1) dps'
        mkUnif' arr arr' =
            A.array ((0,0), (length dps' - 1, length dps' - 1))
                       ([((adjust x,adjust y), sigma) | ((x,y), sigma) <- assocs arr
                                                      , x /= i, y /= i] ++
                        concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
--                                 [ (in1, computeDPUnifier typ rules a_dps' in1)
--                                 , (in2, computeDPUnifier typ rules a_dps' in2)]
                                 | j <- new_nodes, k <- [0..l_dps'-1]
                                 , let in1 = (j,k), let in2 = (k,j)])
        adjust x = if x < i then x else x-1
        l_dps'   = length dps'
        gr'      = buildG (0, l_dps' - 1)
                   ([(adjust x,adjust y) | (x,y) <- edges gr, x/=i, y/=i] ++
                    [(n,n') | n' <- new_nodes
                            , (n,m) <- edges gr, n/=i, m == i ] ++
                    [(n',n) | n <- gr ! i, n' <- new_nodes] ++
                    [(n',n'') | n' <- new_nodes, n'' <- new_nodes, i `elem` gr ! i])

    (unif_new :!: unifInv_new) <- computeDPUnifiers typ trs dps'
    let unif'    = mkUnif' unif    unif_new     `asTypeOf` unif
        unifInv' = mkUnif' unifInv unifInv_new  `asTypeOf` unif
        dptrs'   = dpTRS'' a_dps' gr' (unif' :!: unifInv')
    return dptrs'

  where
    (dps1,_:dps2) = splitAt i (elems dps)
    new_nodes= [l_dps - 1 .. l_dps + l_newdps - 2]
    l_dps    = snd (bounds dps) + 1
    l_newdps = length newdps

expandDPair typ trs dps@TRS{} i newdps = tRS dps'
  where
    dps'          = dps1 ++ dps' ++ dps2
    (dps1,_:dps2) = splitAt i (rules dps)

rulesArray (DPTRS dps _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

instance Ord id => HasSignature (NarradarTRS id v) id where
    getSignature (TRS         _ sig) = sig
    getSignature (PrologTRS   _ sig) = sig
    getSignature (DPTRS   _ _ _ sig) = sig

instance (Ord v, Ord id) => Monoid (NarradarTRS id v) where
    mempty                        = TRS mempty mempty
    mappend (TRS r1 _) (TRS r2 _) = let rr = r1 `mappend` r2 in
                                    TRS rr (getSignature rr)
    mappend (PrologTRS r1 _) (PrologTRS r2 _) =
       let rr = r1 `mappend` r2 in PrologTRS rr (getSignature (snd <$> toList rr))
    mappend (DPTRS r1 e1 _ _) (DPTRS r2 e2 _ _) =
       let rr = elems r1 `mappend` elems r2 in TRS (Set.fromList rr) (getSignature rr)
    mappend emptytrs trs | null (rules emptytrs) = trs
    mappend trs emptytrs | null (rules emptytrs) = trs
    mappend x y = tRS (rules x `mappend` rules y)

instance (Ord v, Ppr v, Ppr id) => Ppr (NarradarTRS id v) where
    ppr trs@TRS{}   = vcat $ map ppr $ rules trs
    ppr trs@DPTRS{} = vcat $ map ppr $ rules trs
    ppr trs@PrologTRS{} = vcat $ map ppr $ rules trs


instance (Ord id, Ord v) => ApplyAF (NarradarTRS id v) id where
    apply af (PrologTRS  cc sig) = let trs' = PrologTRS (Set.mapMonotonic (\(c,r) ->(c, apply af r)) cc) (getSignature $ rules trs') in trs'
    apply af trs@TRS{}           = tRS$ apply af <$$> rules trs
    apply af trs@DPTRS{}         = tRS$ apply af <$$> rules trs

-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, but it does to make GHC happy (avoid recursive module dependencies)

ren :: (Enum v, Traversable t, MonadFresh v m) => Term t v -> m(Term t v)
ren = foldTermM (\_ -> return `liftM` freshVar) (return . Impure)

-- Use unification instead of just checking if it is a defined symbol
-- This is not the icap defined in Rene Thiemann, as it does not integrate the REN function
icap :: (Enum v, Ord v, Unify t, HasRules t v trs, MonadFresh v m) => trs -> Term t v -> m(Term t v)
icap trs = foldTermM return2 go where
  go t = if any (unifies (Impure t) . lhs) (rules trs) then return `liftM` freshVar else return (Impure t)
                  -- In Rene Thiemann, icap inserts a fresh variable here in some cases
                  -- but unfortunately we lack a good infrastructure for doing this

collapsing trs = any (isVar.rhs) (rules trs)

-- ---------------------
-- Usable rules of a TRS
-- ---------------------

-- Assumes Innermost or Constructor Narrowing
-- TODO Extend to work with Q-narrowing to discharge those assumptions
iUsableRulesM :: (Ord v, Enum v, Ord (Term t v), HasRules t v trs, AF.ApplyAF (Term t v) id, AF.ApplyAF trs id, Unify t, Traversable t, MonadFresh v m) =>
                 trs -> Maybe (AF.AF_ id) -> [Term t v] -> m [Rule t v]
iUsableRulesM trs Nothing = liftM F.toList . go mempty where
--  usableRules acc t | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = return acc
  go acc (t:rest) = evalFree (\_ -> go acc rest) f t where
      f in_t = do
         t'  <- wrap `liftM` (icap trs `T.mapM` in_t)
         let rr  = [ r | r <- rules trs, lhs r `unifies` t']
             new = Set.difference (Set.fromList rr) acc
         go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])

iUsableRulesM trs (Just pi) = liftM F.toList . go mempty . map(AF.apply pi) where
  pi_rules = [(AF.apply pi r, r) | r <- rules trs]
  pi_trs   = AF.apply pi trs
--  usableRules acc (AF.apply pi -> t) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = return acc
--  go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc (t:rest) = evalFree (\_ -> go acc rest) f t where
     f in_t = do
        t' <- wrap `liftM` (icap pi_trs `T.mapM` in_t)
        let rr = Set.fromList
                [r | (pi_r, r) <- pi_rules
                  , t' `unifies` lhs pi_r]
            new = Set.difference rr acc
        go (new `mappend` acc) (mconcat [AF.apply pi . rhs <$> F.toList new, directSubterms t, rest])

iUsableRules :: (Ord v, Enum v, Ord (Term t v), HasRules t v trs, GetVars v trs, AF.ApplyAF (Term t v) id, AF.ApplyAF trs id, Unify t, Traversable t) =>
                 trs -> Maybe (AF.AF_ id) -> [Term t v] -> [Rule t v]
iUsableRules trs mb_pi = runIcap trs . iUsableRulesM trs mb_pi

{-
iUsableRules_correct trs (Just pi) = F.toList . go mempty where
  pi_trs = AF.apply pi trs
  --go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t:rest) = evalFree (\_ -> go acc rest) f t where
    f t0
      | t@(Impure in_t) <- AF.apply pi t0
      , rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , wrap(runSupply' (icap pi_trs `T.mapM` in_t) ids) `unifies` lhs pi_r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])
  ids = [0..] \\ (concatMap.concatMap) collectVars (rules trs)
-}
-- -------------
-- Utils
-- -------------

runIcap :: Enum v => GetVars v thing => thing -> State (Substitution t (Either v v), [v]) a -> a
runIcap t m = evalState m (mempty, freshVars) where freshVars = map toEnum [maximum (map fromEnum (getVars t)).. ]

#ifdef HOOD
instance (Show id, Ord id, Show v, Ppr f) => Observable (NarradarTRS id v) where
  observer (DPTRS dps gr (unif :!: unifInv) sig) = send "DPTRS" (return (\dps unif -> DPTRS dps gr (unif :!: unifInv) sig) << dps << unif)
  observer x = observeBase x
#endif