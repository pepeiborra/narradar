{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Narradar.Types.Problem (
          module Narradar.Types.Problem,
          module Narradar.Constraints.ICap,
          module Narradar.Constraints.UsableRules) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Exception (assert)
import Control.Monad.List
import Control.Monad.State
import Data.Array as A
import Data.Graph as G (Graph, edges, buildG)
import Data.Foldable as F (Foldable(..), toList)
import Data.Maybe (isJust, isNothing)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable as T
import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import Text.XHtml as H hiding ((!), rules, text)
import qualified Text.XHtml as H
import Prelude as P hiding (mapM, pi, sum)
import qualified Prelude as P

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.TRS
import Narradar.Framework.Ppr as Ppr
import Narradar.Utils
import Narradar.Types.Term hiding ((!))
import Narradar.Constraints.ICap
import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Types.Var

import Data.Term.Rules

-- -------------------------
-- Constructing DP problems
-- -------------------------
type NarradarProblem typ t = Problem typ (NarradarTRS t Var)
type NProblem typ id = NarradarProblem typ (TermF id)

mkNewProblem :: ( HasRules (TermF id) Var trs
                , Ord id, Pretty (Identifier id), Pretty typ
                , Traversable (Problem typ)
                , MkDPProblem typ (NTRS (Identifier id))
                , NCap (Identifier id) (typ, NTRS (Identifier id))
                , NUsableRules (Identifier id) (typ, NTRS (Identifier id), NTRS (Identifier id))
                ) => typ -> trs -> NProblem typ (Identifier id)
mkNewProblem typ trs = mkDPProblem' typ  rr' (getPairs typ rr') where
   rr' = mapTermSymbols IdFunction <$$> rules trs

mkDerivedProblem typ p = mkDPProblem typ (getR p) (getP p)

mkDPProblem' :: ( Enum v, Ord v, Pretty v
                , rr ~ [Rule t v]
                , ntrs ~ NarradarTRS t v
                , Unify t, HasId t, Ord (Term t v)
                , MkDPProblem typ (NarradarTRS t v), Traversable (Problem typ)
                , ICap t v (typ, ntrs)
                , IUsableRules t v (typ, ntrs, ntrs)
                , Pretty (t(Term t v)), Pretty typ
                , IsTRS t v trs
                ) => typ -> trs -> trs -> Problem typ (NarradarTRS t v)

{-# SPECIALIZE mkDPProblem' :: (Ord id, Pretty id, Pretty typ, MkDPProblem typ (NTRS id), Traversable (Problem typ)
                               ,NCap id (typ, NTRS id), NUsableRules id (typ, NTRS id, NTRS id)
                               ) =>
                               typ -> NTRS id -> NTRS id -> Problem typ (NTRS id) #-}

mkDPProblem' typ (rules -> rr) (rules -> dps) = mkDPProblem typ (tRS rr) dptrs
  where
      dptrs = dpTRS typ rr dps



-- ---------------------------
-- Computing Dependency Pairs
-- ---------------------------
class GetPairs typ where
  getPairs :: ( HasRules t v trs, HasSignature trs, t ~ f (Identifier id), Ord id
              , Foldable t, MapId f, HasId t
              , SignatureId trs ~ TermId t)
               => typ -> trs -> [Rule t v]
instance GetPairs typ where
  getPairs _ trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isRootDefined trs) r]

-- ----------------------------------------
-- Computing the estimated Dependency Graph
-- ----------------------------------------

getEDG :: (Ord v, Enum v
          ,HasId t, Unify t
          ,Ord (Term t v)
          ,Pretty (t(Term t v)), Pretty typ, Pretty v
          ,IsDPProblem typ, Traversable (Problem typ)
          ,ICap t v (typ, NarradarTRS t v)
          ,IUsableRules t v (typ, NarradarTRS t v, NarradarTRS t v)
          ) => Problem typ (NarradarTRS t v) -> G.Graph
getEDG p = filterSEDG p $ getdirectEDG p

getdirectEDG :: (Traversable (Problem typ)
                ,IsDPProblem typ, Enum v, Ord v, Unify t
                ,ICap t v (typ, NarradarTRS t v)
                ,Pretty v, Pretty (t(Term t v)), Pretty typ
                ) => Problem typ (NarradarTRS t v) -> G.Graph
getdirectEDG p@(getP -> DPTRS dps _ (unif :!: _) _) =
    assert (isValidUnif p) $
    G.buildG (A.bounds dps) [ xy | (xy, Just _) <- A.assocs unif]

getDirectEDG p = G.buildG (0, length dps - 1) edges where
  dps = rules $ getP p
  edges = runIcap p $ runListT $ do
                (x, _ :-> r) <- liftL $ zip [0..] dps
                (y, l :-> _) <- liftL $ zip [0..] dps
                r' <- lift(getFresh r >>= icap p)
                guard (unifies l r')
                return (x,y)
  liftL = ListT . return

filterSEDG :: (Ord v, Enum v
              ,HasId t, Unify t
              ,Ord (Term t v)
              ,IsDPProblem typ, Traversable (Problem typ)
              ,ICap t v (typ, NarradarTRS t v)
              ,IUsableRules t v (typ, [Rule t v], [Rule t v])
              ) => Problem typ (NarradarTRS t v) -> G.Graph -> G.Graph
filterSEDG p gr | isCollapsing (getP p) = gr
filterSEDG (getP -> dptrs@DPTRS{}) gr =
    G.buildG (A.bounds gr)
               [ (i,j) | (i,j) <- G.edges gr
                       , isJust (dpUnifyInv dptrs j i)]

filterSEDG p gr = G.buildG (bounds gr) edges where
  typ = getProblemType p
  dps = A.listArray (bounds gr) (rules $ getP p)
  edges = runIcap p $ runListT $ do
                trs'   <- lift $ getFresh (rules $ getR p)
                (i, j) <- liftL (G.edges gr)
                let _ :-> r = dps A.! i
                    l :-> _ = dps A.! j
                (_,trs_u,_) <- iUsableRulesM (typ, trs', A.elems dps) [r]
                let trs_inv = swapRule <$> trs_u
                l'  <- lift (icap (typ, trs_inv) l)
                guard (unifies l' r)
                return (i,j)
  liftL = ListT . return

emptyArray :: (Num i, Ix i) => Array i e
emptyArray = A.listArray (0,-1) []

-- ----------------
-- Output
-- ----------------

instance (IsDPProblem p, Pretty p, Pretty trs) => Pretty (Problem p trs) where
    pPrint p =
            pPrint (getProblemType p) <+> text "Problem" $$
            text "TRS:" <+> pPrint (getR p) $$
            text "DPS:" <+> pPrint (getP p)

instance (IsDPProblem typ, HTML typ, HTMLClass typ, HasRules t v trs, Pretty (Term t v)
         ) => HTML (Problem typ trs) where
    toHtml p
     | null $ rules (getP p) =
        H.table H.! [htmlClass typ] << (
            H.td H.! [H.theclass "problem"] << H.bold << typ </>
            H.td H.! [H.theclass "TRS_TITLE" ] << "Rules"</> aboves' (rules $ getR p) </>
                 "Dependency Pairs: none")
     | otherwise =
        H.table H.! [htmlClass typ] << (
            H.td H.! [H.theclass "problem"] << H.bold << typ </>
            H.td H.! [H.theclass "TRS_TITLE" ] << "Rules" </>
                 aboves' (rules $ getR p) </>
            H.td H.! [H.theclass "DPS" ] << "Dependency Pairs" </>
                 aboves' (rules $ getP p))

     where typ = getProblemType p

instance (Pretty (Term t v)) =>  HTMLTABLE (Rule t v) where
    cell (lhs :-> rhs ) = td H.! [theclass "lhs"]   << show (pPrint lhs) <->
                          td H.! [theclass "arrow"] << (" " +++ H.primHtmlChar "#x2192" +++ " ") <->
                          td H.! [theclass "rhs"]   << show (pPrint rhs)

instance HTMLTABLE String where cell = cell . toHtml

aboves' [] = cell noHtml
aboves' xx = aboves xx

class HTMLClass a where htmlClass :: a -> HtmlAttr


-- -------------------
-- Narradar instances
-- -------------------

instance (Ord v, ExtraVars v trs, IsDPProblem p) =>  ExtraVars v (Problem p trs) where
  extraVars p = extraVars (getP p) `mappend` extraVars (getR p)

instance (ApplyAF trs, IsDPProblem p) => ApplyAF (Problem p trs) where
    type AFId (Problem p trs) = AFId trs
    apply af = fmap (apply af)

-- ------------------------------
-- Data.Term framework instances
-- ------------------------------

getSignatureProblem p = getSignature (getR p) `mappend` getSignature (getP p)

instance (Ord v, IsDPProblem typ, HasRules t v trs, Foldable (Problem typ)) => HasRules t v (Problem typ trs) where
    rules = foldMap rules

instance (Ord v, GetFresh t v trs, Traversable (Problem typ)) => GetFresh t v (Problem typ trs) where getFreshM = getFreshMdefault

instance (Ord v, GetVars v trs, Traversable (Problem typ)) => GetVars v (Problem typ trs) where getVars = foldMap getVars

instance (HasSignature trs, IsDPProblem typ) => HasSignature (Problem typ trs) where
  type SignatureId (Problem typ trs) = SignatureId trs
  getSignature p = getSignature (getR p) `mappend` getSignature (getP p)

-- ------------------------------------
-- Dealing with the pairs in a problem
-- ------------------------------------

expandDPair :: ( problem ~ Problem typ
               , trs ~ NarradarTRS t v
               , HasId t, Foldable t, Unify t, Ord (Term t v), Ord v, Enum v
               , Traversable problem, MkDPProblem typ trs
               , ICap t v (typ, trs)
               , IUsableRules t v (typ, trs, trs)
               , Pretty (t(Term t v)), Pretty v, Pretty typ
               ) =>
               problem (NarradarTRS t v) -> Int -> [Rule t v] -> problem (NarradarTRS t v)

expandDPair p@(getP -> DPTRS dps gr (unif :!: unifInv) _) i (filter (`notElem` elems dps) . snub -> newdps)
 = runIcap (rules p ++ newdps) $ do
    let dps'     = dps1 ++ dps2 ++ newdps
        l_dps'   = l_dps + l_newdps
        a_dps'   = A.listArray (0,l_dps') dps'
        mkUnif' arr arr' =
            A.array ((0,0), (l_dps', l_dps'))
                       ([((adjust x,adjust y), sigma) | ((x,y), sigma) <- assocs arr
                                                      , x /= i, y /= i] ++
                        concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
                                 | j <- new_nodes, k <- [0..l_dps']
                                 , let in1 = (j,k), let in2 = (k,j)])
        adjust x = if x < i then x else x-1

    unif_new :!: unifInv_new <- computeDPUnifiers (getProblemType p) (rules $ getR p) dps'
    let unif'    = mkUnif' unif    unif_new
        unifInv' = mkUnif' unifInv unifInv_new
        dptrs'   = dpTRS' a_dps' (unif' :!: unifInv')
--      dptrs_new= dpTRS' a_dps' (unif_new :!: unifInv_new)

    let res = setP dptrs' p

    assert (isValidUnif p) $
     assert (isValidUnif res) $
     return res

 where
   (dps1,_:dps2) = splitAt i (elems dps)
   new_nodes= [l_dps .. l_dps + l_newdps]
   l_dps    = assert (fst (bounds dps) == 0) $ snd (bounds dps)
   l_newdps = length newdps - 1

expandDPair p i newdps = setP (tRS dps') p
  where
    dps'          = dps1 ++ dps2 ++ newdps
    (dps1,_:dps2) = splitAt i (rules $ getP p)


class MkDPProblem typ trs => InsertDPairs typ trs where
    insertDPairs :: Problem typ trs -> trs -> Problem typ trs

insertDPairsDefault ::
         (trs ~ NTRS id
         ,MkDPProblem typ trs, Pretty typ, Traversable (Problem typ)
         ,Pretty id, Eq id
         ,NUsableRules id (typ, trs, trs)
         ,NCap id (typ, trs)
         ) => NProblem typ id -> NTRS id -> NProblem typ id

insertDPairsDefault p@(getP -> DPTRS dps _ (unif :!: unifInv) sig) newPairs
    = runIcap (getVars p `mappend` getVars newPairs) $ do
      let (_,l_dps) = bounds dps
          l_newPairs  = length $ rules newPairs
          dps'      = A.elems dps ++ rules newPairs
          l_dps'    = l_dps + l_newPairs
          a_dps'    = A.listArray (0,l_dps') dps'
          new_nodes= [l_dps + 1 .. l_dps']
          mkUnif arr arr' =
            A.array ((0,0), (l_dps', l_dps'))
                    (assocs arr ++
                     concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
                                 | j <- new_nodes, k <- [0..l_dps']
                                 , let in1 = (j,k), let in2 = (k,j)])

      unif_new :!: unifInv_new <- computeDPUnifiers (getProblemType p) (getR p) (tRS dps')
      let unif'    = mkUnif unif unif_new
          unifInv' = mkUnif unifInv unifInv_new

          dptrs'   = dpTRS' a_dps' (unif' :!: unifInv')
          p'       = setP dptrs' p
          gr'      = getEDG p'

      return p'



-- -------------
-- Sanity Checks
-- -------------
isValidUnif :: ( p   ~ Problem typ
               , Ord v, Enum v, Unify t
               , Traversable p, IsDPProblem typ, Pretty typ
               , ICap t v (typ, NarradarTRS t v)
               , Pretty v, Pretty (t(Term t v))
               ) => p (NarradarTRS t v) -> Bool
isValidUnif p@(getP -> DPTRS dps _ (unif :!: _) _)
  | valid = True
  | otherwise = pprTrace (text "Warning: invalid set of unifiers" $$
                          text "Problem type:" <+> pPrint (getProblemType p) $$
                          text "DPS:"      <+> pPrint (elems dps) $$
                          text "Unifiers:" <+> pPrint unif        $+$ Ppr.empty $+$
                          text "Computed:" <+> pPrint unif'       $+$ Ppr.empty $+$
                          text "Expected:" <+> pPrint (fmap (\b -> if b then "Y" else "N") validUnif)
                         )
                         valid
  where
  liftL = ListT . return
  l     = length (rules $ getP p) - 1
  unif' = runIcap (getP p) (getFresh (getR p) >>= \rr' -> computeDirectUnifiers (getProblemType p,rr') (getP p))
  validUnif = array ( (0,0), (l,l)) $ runIcap p $ runListT $ do
            (x, _ :-> r) <- liftL $ A.assocs dps
            (y, l :-> _) <- liftL $ A.assocs dps
            r' <- getFresh r >>= icap p
--            pprTrace (text "unify" <+> pPrint l <+> pPrint r') (return ())
            return ((x,y),unifies l r')

  valid = and $ zipWith (\subst unifies -> if unifies then isJust subst else isNothing subst) (elems unif) (elems validUnif)


isValidUnif _ = True


noDuplicateEdges gr = Set.size(Set.fromList (edges gr)) == length (edges gr)