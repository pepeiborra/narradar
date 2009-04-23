{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module Narradar.TRS where

import Control.Applicative
import Control.Monad
import Control.Monad.List
import Control.Monad.State
import Control.Monad.Supply
import Control.Parallel.Strategies
import Data.Array.IArray as A
import Data.Graph (Graph, edges, buildG)
import Data.Foldable as F (Foldable, foldMap, toList, concatMap)
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

import TRS hiding (Ppr, ppr, unify, unifies, (!))
import qualified TRS
import Narradar.ArgumentFiltering (apply, ApplyAF(..))
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPIdentifiers
import Narradar.Labellings
import Narradar.ProblemType
import Narradar.Unify
import Narradar.Utils
import qualified Language.Prolog.Syntax as Prolog

#ifdef HOOD
import Debug.Observe
#endif

type DP a = Rule a

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

data NarradarTRS id f where
    TRS       :: (Ord id, TRSC f, T id :<: f) => Set (Rule f)                                  -> Signature id -> NarradarTRS id f
    PrologTRS :: (Ord id, TRSC f, T id :<: f) => Set (String, Rule f)                          -> Signature id -> NarradarTRS id f
    DPTRS     :: (Ord id, TRSC f, T id :<: f) => Array Int (Rule f) -> !Graph -> Unifiers f :!: Unifiers f -> Signature id -> NarradarTRS id f

type Unifiers        f = Array (Int,Int) (Maybe (Subst f))

instance (Ord id, Ord (Term f), TRSC f, T id :<: f) => Ord (NarradarTRS id f) where
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BasicId) #-}
    {-# SPECIALIZE instance Ord(NarradarTRS Id  BBasicId) #-}
    {-# off SPECIALIZE instance Ord(NarradarTRS LId BBasicLId) #-}
    compare TRS{} _             = GT
    compare DPTRS{} TRS{}       = LT
    compare DPTRS{} PrologTRS{} = GT
    compare PrologTRS{} _       = LT
    compare (TRS rr1 _)       (TRS rr2 _)       = compare rr1 rr2
    compare (PrologTRS rr1 _) (PrologTRS rr2 _) = compare rr1 rr2
    compare (DPTRS rr1 _ _ _) (DPTRS rr2 _ _ _)   = compare rr1 rr2

instance (Ord id, T id :<: f, TRSC f) => TRS (NarradarTRS id f) id f where
    {-# SPECIALIZE instance TRS(NarradarTRS Id BasicId) Id BasicId #-}
    {-# SPECIALIZE instance TRS(NarradarTRS Id BBasicId) Id BBasicId #-}
    {-# off SPECIALIZE instance TRS(NarradarTRS LId BBasicLId) LId BBasicLId #-}
    rules(TRS       rr _)   = toList rr
    rules(PrologTRS rr _)   = map snd (toList rr)
    rules(DPTRS     rr _ _ _) = elems rr
    tRS = narradarTRS

tRS' rr sig  = TRS (Set.fromList rr) sig

prologTRS :: forall id f. (Ord id, TRSC f, T id :<: f) => [(String, Rule f)] -> NarradarTRS id f
prologTRS rr = prologTRS' (Set.fromList rr)

prologTRS' :: forall id f. (Ord id, TRSC f, T id :<: f) => Set(String, Rule f) -> NarradarTRS id f
prologTRS' rr = PrologTRS rr (getSignature (snd <$> toList rr))

{-# SPECIALIZE narradarTRS ::  [Rule BBasicId] -> NarradarTRS Id BBasicId #-}
narradarTRS rules = TRS (Set.fromList rules) (getSignature rules)
--dpTRS :: (T id :<: d) => ProblemType id -> NarradarTRS id f -> [DP f] -> Graph -> NarradarTRS id f
dpTRS typ trs dps edges = dpTRS' typ trs dps' edges
  where dps' = listArray (0, length dps - 1) (refreshRules [0..] dps)

-- | Assumes that the rules have already been renamed apart
--dpTRS' :: (T id :<: d) => ProblemType id -> NarradarTRS id f -> Array Int (DP f) -> Graph -> NarradarTRS id f
dpTRS' typ trs dps edges = DPTRS dps edges (computeDPUnifiers typ trs $ elems dps)
                                           (getSignature $ elems dps)

-- | Assumes that the rules have already been renamed apart
dpTRS'' dps edges unifiers = DPTRS dps edges unifiers (getSignature $ elems dps)

refreshRules ids  = (`runSupply'` ids) . mapM doRule where
        doRule r = do
          let vv = foldMap vars' r
          newvv <- replicateM (length vv) next
          return (replace (Prelude.zipWith leftName vv newvv) <$> r)

        leftName v1 i2 = (v1, var' (varName v1) i2)
--        leftName v1 i2 = (v1, var i2)

        varName (open -> Just (Var n _)) = n
        varName _ = Nothing

--computeDPUnifiers _ _ dps | trace ("computeDPUnifiers dps=" ++ show(length dps)) False = undefined
computeDPUnifiers :: (DPMark f, TRS trs id f, ApplyAF trs id, MonadPlus m, unif ~ Array (Int,Int) (m(Subst f)))=> ProblemType id -> trs -> [DP f] -> unif :!: unif
computeDPUnifiers typ trs dps = unif :!: unifInv where
   unif = array ( (0,0), (length dps -1 , length dps - 1) )
           [((x,y), unify l (if x/=y then r' else rename r'))
              | (x, _ :-> r) <- zip [0..] dps
              , (y, l :-> _) <- zip [0..] dps
              , let r' = runSupply' (icap trs r >>= mbren) ids ]
   unifInv = array ( (0,0), (length dps -1 , length dps - 1) )
           [((x,y), unify r (if x/=y then l' else rename l'))
              | (x, _ :-> r) <- zip [0..] dps
              , (y, l :-> _) <- zip [0..] dps
              , let trs' = tRS (swapRule <$> mbUsableRules [r]) `asTypeOf` trs
              , let l' = runSupply' (icap trs' l >>= ren) ids ]

   rename t = head $ runSupply' (variant [t]) ids
   ids = [0..] \\ (concatMap.concatMap) collectVars dps
   (mbren, mbUsableRules) = if (isBNarrowing .|. isGNarrowing) typ
                              then (return,iUsableRules trs Nothing)
                              else (ren,const (rules trs))

restrictDPTRS (DPTRS dps gr (unif :!: unifInv) sig) indexes =
    DPTRS dps' gr' unif' sig
  where
   newIndexes = Map.fromList (zip indexes [0..])
   nindexes   = length indexes -1
   dps'       = extractIxx dps indexes
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

--expandDPair :: ProblemG id f -> Int -> [DP f] -> ProblemG id f
--expandDPair (Problem typ rules (DPTRS dps gr unif sig)) i newdps | trace ("expandDPair i="++ show i ++ " dps=" ++ show(numElements dps) ++ " newdps=" ++ show (length newdps)) False = undefined
expandDPair typ trs (DPTRS dps gr (unif :!: unifInv) sig) i newdps =
    dptrs' `demanding` rnf unif' `demanding` rnf unifInv'
  where
    dptrs'   = dpTRS'' a_dps' gr' (unif' :!: unifInv')
    unif'    = mkUnif' unif    unif_new     `asTypeOf` unif
    unifInv' = mkUnif' unifInv unifInv_new  `asTypeOf` unif
    a_dps'   = A.listArray (0,length dps' - 1) dps'
    dps'     = dps1 ++  dps2 ++ refreshRules ids newdps
    ids      = [0..] \\ (concatMap.concatMap) collectVars dps
    (dps1,_:dps2) = splitAt i (elems dps)

    gr' = buildG (0, l_dps' - 1)
                   ([(adjust x,adjust y) | (x,y) <- edges gr, x/=i, y/=i] ++
                    [(n,n') | n' <- new_nodes
                            , (n,m) <- edges gr, n/=i, m == i ] ++
                    [(n',n) | n <- gr ! i, n' <- new_nodes] ++
                    [(n',n'') | n' <- new_nodes, n'' <- new_nodes, i `elem` gr ! i])

    mkUnif' arr arr' =
       A.array ((0,0), (length dps' - 1, length dps' - 1))
                       ([((adjust x,adjust y), sigma) | ((x,y), sigma) <- assocs arr
                                                      , x /= i, y /= i] ++
                        concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
--                                 [ (in1, computeDPUnifier typ rules a_dps' in1)
--                                 , (in2, computeDPUnifier typ rules a_dps' in2)]
                                 | j <- new_nodes, k <- [0..l_dps'-1]
                                 , let in1 = (j,k), let in2 = (k,j)])
    (unif_new :!: unifInv_new) = computeDPUnifiers typ trs dps'
    adjust x = if x < i then x else x-1
    !l_dps'   = length dps'
    !l_dps    = snd (bounds dps) + 1
    !l_newdps = length newdps
    new_nodes= [l_dps - 1 .. l_dps + l_newdps - 2]

expandDPair typ trs dps@TRS{} i newdps = tRS dps' `asTypeOf` dps where
    dps'          = dps1 ++ dps' ++ dps2
    (dps1,_:dps2) = splitAt i (rules dps)

rulesArray (DPTRS dps _ _ _) = dps
rulesArray (TRS rules _)   = listArray (0, Set.size rules - 1) (Set.toList rules)

instance Ord id => HasSignature (NarradarTRS id f) id where
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BasicId) Id #-}
    {-# SPECIALIZE instance HasSignature(NarradarTRS Id BBasicId) Id #-}
    {-# off SPECIALIZE instance HasSignature(NarradarTRS LId BBasicLId) LId #-}
    getSignature (TRS         _ sig) = sig
    getSignature (PrologTRS   _ sig) = sig
    getSignature (DPTRS   _ _ _ sig) = sig

instance (T id :<: f, Ord id, TRSC f) => Monoid (NarradarTRS id f) where
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BasicId) #-}
    {-# SPECIALIZE instance Monoid(NarradarTRS Id BBasicId) #-}
    {-# off SPECIALIZE instance Monoid(NarradarTRS LId BBasicLId) #-}
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

instance (T id :<: f, Ord id, TRSC f) =>  Size (NarradarTRS id f) where size = sizeTRS

instance TRS.Ppr f      => Ppr (NarradarTRS id f) where
    ppr trs@TRS{}   = vcat $ map ppr $ rules trs
    ppr trs@DPTRS{} = vcat $ map ppr $ rules trs

instance (Ord id) => ApplyAF (NarradarTRS id f) id where
    {-# SPECIALIZE instance ApplyAF (NarradarTRS LPId BasicLPId) LPId #-}
    apply af (PrologTRS  cc sig) = let trs' = PrologTRS (Set.mapMonotonic (\(c,r) ->(c, apply af r)) cc) (getSignature $ rules trs') in trs'
    apply af trs@TRS{}           = tRS$ apply af <$$> rules trs
    apply af trs@DPTRS{}         = tRS$ apply af <$$> rules trs

-- -----------------
-- Cap & friends
-- -----------------
-- This should not live here, but we need to make GHC happy (avoid recursive module dependencies)

ren :: (Var :<: f, IsVar f, HashConsed f, Traversable f, MonadSupply Int m) => Term f -> m(Term f)
ren = foldTermM f where
    f t | Just Var{} <- prj t = var `liftM`  next
        | otherwise           = return (inject t)

-- Use unification instead of just checking if it is a defined symbol
-- This is not the icap defined in Rene Thiemann, as it does not integrate the REN function
icap :: forall trs f id m. (Ord id, TRSC f, TRS trs id f, MonadSupply Int m) => trs -> Term f -> m(Term f)
icap trs = foldTermM go where
  go in_t | Just (T (f::id) tt) <- prj in_t, t <- inject in_t
       = if  any (unifies t . lhs) (rules trs) then var `liftM` next else return t
  go v = return (inject v)
                  -- In Rene Thiemann, icap inserts a fresh variable here in some cases
                  -- but unfortunately we lack a good infrastructure for doing this

collapsing trs = any (isVar.rhs) (rules trs)


-- ---------------------
-- Usable rules of a TRS
-- ---------------------

-- Assumes Innermost or Constructor Narrowing
-- TODO Extend to work with Q-narrowing to discharge those assumptions
iUsableRules :: (Ord id, TRSC f, TRS trs id f, AF.ApplyAF trs id, DPMark f) => trs -> Maybe (AF.AF_ id) -> [Term f] -> [Rule f]
iUsableRules trs Nothing = F.toList . go mempty where
--  usableRules acc t | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t@(In in_t):rest)
      | isVar t   = go acc rest
      | otherwise =
         let t'  = hIn $ runSupply' (icap trs `T.mapM` in_t) ids
             rr  = [ r | r <- rules trs, lhs r `unifies` t']
             new = Set.difference (Set.fromList rr) acc
         in go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])

  ids = [0..] \\ (concatMap.concatMap) collectVars (rules trs)


iUsableRules trs (Just pi) = F.toList . go mempty . map(AF.apply pi) where
  pi_rules = [(AF.apply pi r, r) | r <- rules trs]
  pi_trs   = AF.apply pi trs
--  usableRules acc (AF.apply pi -> t) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
--  go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined 
  go acc (t@(In in_t):rest)
      | isVar t = go acc rest
      | rr   <- Set.fromList [r | (pi_r, r) <- pi_rules
                                , hIn (runSupply' (icap pi_trs `T.mapM` in_t) ids) `unifies` lhs pi_r]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [AF.apply pi . rhs <$> F.toList new, directSubterms t, rest])

  ids = [0..] \\ (concatMap.concatMap) collectVars (rules trs)

iUsableRules_correct trs (Just pi) = F.toList . go mempty where
  pi_trs = AF.apply pi trs
  --go acc (t:_) | trace ("usableRules acc=" ++ show acc ++ ",  t=" ++ show t) False = undefined
  go acc [] = acc
  go acc (t:rest)
      | isVar t = go acc rest
      | t@(In in_t) <- AF.apply pi t
      , rr   <- Set.fromList [r | (pi_r, r) <- zip (rules pi_trs) (rules trs)
                                , hIn(runSupply' (icap pi_trs `T.mapM` in_t) ids) `unifies` lhs pi_r ]
      , new  <- Set.difference rr acc
      = go (new `mappend` acc) (mconcat [rhs <$> F.toList new, directSubterms t, rest])
  ids = [0..] \\ (concatMap.concatMap) collectVars (rules trs)

-- -------------
-- Utils
-- -------------

collectVars :: (Foldable f, IsVar f) => Term f -> [Int]
collectVars = catMaybes . map uniqueId . subterms


#ifdef HOOD
instance (Show id, TRSC f, Ord id, T id :<: f, TRS.Ppr f) => Observable (NarradarTRS id f) where
  observer (DPTRS dps gr (unif :!: unifInv) sig) = send "DPTRS" (return (\dps unif -> DPTRS dps gr (unif :!: unifInv) sig) << dps << unif)
  observer x = observeBase x
#endif