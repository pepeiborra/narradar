{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Narradar.Types.Problem (
--          module MuTerm.Framework.Problem,
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
import Narradar.Types.Term hiding ((!))
import Narradar.Framework (FrameworkExtension(..))
import Narradar.Framework.Ppr as Ppr
import Narradar.Utils
import Narradar.Constraints.ICap
import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Types.Var

import qualified Data.Term as Family
import qualified Data.Rule.Family as Family
import Data.Term.Rules

-- -------------------------
-- Constructing DP problems
-- -------------------------
type NarradarProblem typ t = Problem typ (NarradarTRS t Var)
type NProblem typ id = NarradarProblem typ (TermF id)

-- DODGY !
--type instance Family.Id1 (f id) = id

mkNewProblem ::
    ( HasRules trs
    , Family.Rule trs ~ Rule (TermF id) Var
    , Ord id
    , GetPairs typ
    , MkDPProblem typ (NTRS (DPIdentifier id))
    ) => typ -> trs -> NProblem typ (DPIdentifier id)
mkNewProblem typ trs = mkDPProblem typ  (tRS rr') (tRS pairs) where
--   rr' :: [Rule (TermF (DPIdentifier id)) Var]
   rr'   = mapTermSymbols IdFunction <$$> rules trs
   pairs = getPairs typ rr'

-- ---------------------------
-- Computing Dependency Pairs
-- ---------------------------
class GetPairs typ where
  getPairs :: ( HasRules trs, HasSignature trs
              , Rule t v ~ Family.Rule trs
              , t ~ f (DPIdentifier id)
              , Family.Id trs ~ DPIdentifier id
              , Family.Id1 (f (DPIdentifier id)) ~ DPIdentifier id
              , Ord id
              , Functor t, Foldable t, MapId f, HasId t
              ) => typ -> trs -> [Rule t v]

getPairsDefault ::
    ( HasRules trs, HasSignature trs
    , Rule (f id) v ~ Family.Rule trs
    , id ~ Family.Id trs
    , id ~ Id1 (f id)
    , MapId f, HasId (f id)
    , Foldable (f id), Functor (f id)
    , DPSymbol id
    ) =>
    typ -> trs -> [Rule (f id) v]
getPairsDefault typ trs =
    [ markDP l :-> markDP rp | l :-> r <- rules trs, rp <- collect (isRootDefined trs) r]

-- I know, I'm gonna burn in hell ...
instance (FrameworkExtension ext, GetPairs base) => GetPairs (ext base) where
  getPairs typ = getPairs (getBaseFramework typ)

-- ----------------------------------------
-- Computing the estimated Dependency Graph
-- ----------------------------------------

getEDG :: (Ord v, Enum v, Rename v
          ,HasId t, Unify t
          ,Ord (Term t v)
          ,Pretty (Term t v), Pretty typ, Pretty v
          ,MkDPProblem typ (NarradarTRS t v)
          ,Traversable (Problem typ)
          ,ICap (typ, NarradarTRS t v)
          ,IUsableRules typ (NarradarTRS t v)
          ) => Problem typ (NarradarTRS t v) -> G.Graph
getEDG p@(getP -> DPTRS _ _ gr _ _) = gr
getEDG p = filterSEDG p $ getdirectEDG p

getdirectEDG :: (Traversable (Problem typ)
                ,Enum v, Ord v, Pretty v, Rename v
                ,IsDPProblem typ, Unify t
                ,ICap (typ, NarradarTRS t v)
                ,Pretty (Term t v), Pretty typ
                ) => Problem typ (NarradarTRS t v) -> G.Graph
getdirectEDG p@(getP -> DPTRS dps _ _ (unif :!: _) _) =
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

filterSEDG :: (Ord v, Enum v, Rename v
              ,HasId t, Unify t
              ,Ord (Term t v)
              ,MkDPProblem typ (NarradarTRS t v)
              ,Traversable (Problem typ)
              ,ICap (typ, NarradarTRS t v)
              ,IUsableRules typ (NarradarTRS t v)
              ) => Problem typ (NarradarTRS t v) -> G.Graph -> G.Graph
filterSEDG p gr | isCollapsing (getP p) = gr
filterSEDG (getP -> dptrs@DPTRS{}) gr =
    G.buildG (A.bounds gr)
               [ (i,j) | (i,j) <- G.edges gr
                       , isJust (dpUnifyInv dptrs j i)]

filterSEDG p gr = G.buildG (bounds gr) edges where
  typ = getFramework p
  dps = A.listArray (bounds gr) (rules $ getP p)
  edges = runIcap p $ runListT $ do
                trs'   <- lift $ getFresh (rules $ getR p)
                let p' = setR (tRS trs') p
                (i, j) <- liftL (G.edges gr)
                let _ :-> r = safeAt "filterSEDG" dps i
                    l :-> _ = safeAt "filterSEDG" dps j
                (getR -> trs_u) <- iUsableRulesMp p' [r]
                let trs_inv = swapRule <$> rules trs_u
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
            pPrint (getFramework p) <+> text "Problem" $$
            text "TRS:" <+> pPrint (getR p) $$
            text "DPS:" <+> pPrint (getP p)

instance ( IsDPProblem typ
         , HTML typ
         , HTMLClass typ
         , HasRules trs
         , Rule t v ~ Family.Rule trs
         , v ~ Family.Var trs
         , Pretty v
         , Pretty (t(Term t v))
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

     where typ = getFramework p

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

instance (v ~ Family.Var trs, Ord v, ExtraVars trs, IsDPProblem p
         ) =>  ExtraVars (Problem p trs) where
  extraVars p = extraVars (getP p) `mappend` extraVars (getR p)

instance (MkDPProblem typ (NarradarTRS t v)
         ,Unify t
         ,ApplyAF (Term t v)
         ,Enum v, Ord v, Rename v
         ,IUsableRules typ (NarradarTRS t v)
         ,ICap (typ, NarradarTRS t v)
--         ,AFId (Term t v) ~ AFId (NarradarTRS t v)
         ,Pretty (t(Term t v)), Pretty v
         ) =>
    ApplyAF (Problem typ (NarradarTRS t v))
  where
    apply af p@(getP -> dps@DPTRS{})= mkDPProblem typ trs' dps'
     where
       typ  = getFramework p
       trs' = apply af (getR p)
       dps' = dpTRS typ (trs'  `asTypeOf` getR p) (apply af dps)
{-
instance (ApplyAF trs, IsDPProblem p) => ApplyAF (Problem p trs) where
    type AFId (Problem p trs) = AFId trs
    apply af = fmap (apply af)
-}
-- ------------------------------
-- Data.Term framework instances
-- ------------------------------

getSignatureProblem p = getSignature (getR p) `mappend` getSignature (getP p)

instance (v ~ Family.Var trs, Ord v, IsDPProblem typ, HasRules trs, Foldable (Problem typ)
         ) => HasRules (Problem typ trs) where rules = foldMap rules
instance (v ~ Family.Var trs, Ord v, GetFresh trs, Traversable (Problem typ)
         ) => GetFresh (Problem typ trs) where getFreshM = getFreshMdefault

instance (HasSignature trs, IsDPProblem typ) => HasSignature (Problem typ trs) where getSignature p = getSignature (getR p) `mappend` getSignature (getP p)

-- ------------------------------------
-- Dealing with the pairs in a problem
-- ------------------------------------

expandDPair :: ( v ~ Var
               , HasId t, Unify t, Ord (Term t v)
               , Traversable (Problem typ)
               , MkDPProblem typ (NarradarTRS t v)
               , ICap (typ, NarradarTRS t v)
               , IUsableRules typ (NarradarTRS t v)
               , Pretty (Term t v), Pretty typ
               ) =>
               Problem typ (NarradarTRS t v) -> Int -> [Rule t v] -> Problem typ (NarradarTRS t v)
expandDPair p@(getP -> DPTRS dps rr gr (unif :!: unifInv) _) i (filter (`notElem` elems dps) . snub -> newdps)
 = runIcap (rules p ++ newdps) $ do
    let dps'     = dps1 ++ dps2 ++ newdps
        l_dps'   = l_dps + l_newdps
        a_dps'   = A.listArray (0,l_dps') dps'
        mkUnif' arr arr' =
            A.array ((0,0), (l_dps', l_dps'))
                       ([((adjust x,adjust y), sigma) | ((x,y), sigma) <- assocs arr
                                                      , x /= i, y /= i] ++
                        concat [ [(in1, safeAt "expandPair" arr' in1), (in2, safeAt "expandPair" arr' in2)]
                                 | j <- new_nodes, k <- [0..l_dps']
                                 , let in1 = (j,k), let in2 = (k,j)])
        adjust x = if x < i then x else x-1

    unif_new :!: unifInv_new <- computeDPUnifiers (getFramework p) (getR p) (listTRS dps')
                                         -- The use of listTRS here is important ^^
    let unif'    = mkUnif' unif    unif_new
        unifInv' = mkUnif' unifInv unifInv_new
        dptrs'   = dpTRS' a_dps' rr (unif' :!: unifInv')
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

insertDPairsDefault p newPairs = setP dps' p
  where
   dps' = assert (getR p == rulesUsed (getP p)) $
          insertDPairs' (getFramework p) (getP p) (rules newPairs)

insertDPairs' ::
         (trs ~ NTRS id
         ,MkDPProblem framework trs, Pretty framework, Traversable (Problem framework)
         ,Pretty id, Eq id
         ,NUsableRules framework id
         ,NCap framework id
         ) => framework -> NTRS id -> [Rule (TermF id) Var] -> NTRS id
insertDPairs' framework p@(DPTRS dps rr _ (unif :!: unifInv) sig) newPairs
    = runIcap (getVars p `mappend` getVars newPairs) $ do
      let (zero,l_dps) = bounds dps
          l_newPairs  = length $ rules newPairs
          dps'      = A.elems dps ++ rules newPairs
          l_dps'    = l_dps + l_newPairs
          a_dps'    = A.listArray (0,l_dps') dps'
          new_nodes = [l_dps + 1 .. l_dps']
          (!)       = safeAt "insertDPairsDefault"
          mkUnif arr arr' =
            A.array ((zero,zero), (l_dps', l_dps'))
                    (assocs arr ++
                     concat [ [(in1, arr' ! in1), (in2, arr' ! in2)]
                                 | j <- new_nodes, k <- [zero..l_dps']
                                 , let in1 = (j,k), let in2 = (k,j)])

      unif_new :!: unifInv_new <- computeDPUnifiers framework rr (listTRS dps')
                               -- The use of listTRS here is important ^^
      let unif'    = mkUnif unif unif_new
          unifInv' = mkUnif unifInv unifInv_new

          dptrs'   = dpTRS' a_dps' rr (unif' :!: unifInv')

      return dptrs'


-- -------------
-- Sanity Checks
-- -------------
isValidUnif :: forall typ p t  v .
               ( p   ~ Problem typ
               , Ord v, Enum v, Rename v, Pretty v
               , Unify t
               , Traversable p, IsDPProblem typ, Pretty typ
               , ICap (typ, NarradarTRS t v)
               , Pretty (Term t v)
               ) => p (NarradarTRS t v) -> Bool
isValidUnif p@(getP -> DPTRS dps _ _ (unif :!: _) _)
  | valid = True -- const True (pPrint (undefined :: Term t v))
  | otherwise = pprTrace (text "Warning: invalid set of unifiers" $$
                          text "Problem type:" <+> pPrint (getFramework p) $$
                          text "DPS:"      <+> pPrint (elems dps) $$
                          text "Unifiers:" <+> pPrint unif        $+$ Ppr.empty $+$
                          text "Computed:" <+> pPrint unif'       $+$ Ppr.empty $+$
                          text "Expected:" <+> pPrint (fmap (\b -> if b then "Y" else "N") validUnif)
                         )
                         valid
  where
  liftL = ListT . return
  l     = length (rules $ getP p) - 1
  unif' = runIcap (getP p) (getFresh (getR p) >>= \rr' -> computeDirectUnifiers (getFramework p,rr') (getP p))
  validUnif = array ( (0,0), (l,l)) $ runIcap p $ runListT $ do
            (x, _ :-> r) <- liftL $ A.assocs dps
            (y, l :-> _) <- liftL $ A.assocs dps
            r' <- getFresh r >>= icap p
            pprTrace (text "unify" <+> pPrint l <+> pPrint r') (return ())
            return ((x,y),unifies l r')

  valid = and $ zipWith (\subst unifies -> if unifies then isJust subst else isNothing subst) (elems unif) (elems validUnif)


isValidUnif _ = True


noDuplicateEdges gr = Set.size(Set.fromList (edges gr)) == length (edges gr)