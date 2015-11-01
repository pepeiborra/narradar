{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module Narradar.Types.Problem (
--          module MuTerm.Framework.Problem,
          module Narradar.Types.Problem,
          module Narradar.Constraints.ICap,
          module Narradar.Constraints.UsableRules) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad.List
import Control.Monad.State
import Data.Array as A
import Data.Coerce
import Data.Graph as G (Graph, edges, buildG)
import Data.Foldable as F (Foldable(..), toList)
import Data.Functor1
import Data.Functor.Two
import GHC.Generics(Generic,Generic1)
import Data.Maybe (isJust, isNothing)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Suitable
import Data.Strict.Tuple ((:!:), Pair(..))
import Data.Traversable as T
import Data.Typeable (Typeable)
import qualified Language.Prolog.Syntax as Prolog hiding (ident)
import Text.XHtml as H hiding ((!), rules, text)
import qualified Text.XHtml as H
import Prelude as P hiding (mapM, pi, sum)
import Prelude.Extras

import MuTerm.Framework.Problem
import MuTerm.Framework.Proof

import Narradar.Types.ArgumentFiltering (AF_, ApplyAF(..))
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.DPIdentifiers
import Narradar.Types.TRS
import Narradar.Types.Term hiding ((!))
import Narradar.Framework (FrameworkExtension(..), HasMinimality(..), FrameworkTyp, FrameworkTerm, FrameworkId, FrameworkT, FrameworkVar)
import Narradar.Framework.Ppr as Ppr
import Narradar.Utils hiding (O)
import Narradar.Constraints.ICap
import Narradar.Constraints.Unify
import Narradar.Constraints.UsableRules
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Var

import qualified Data.Term as Family
import qualified Data.Rule.Family as Family
import Data.Term.Rules

import Debug.Hoed.Observe (Observable(..), Observable1(..), Observer(..), nilObserver)

type FrameworkProblem p trs = FrameworkProblem0 p trs

type FrameworkProblemExt p trs =
  ( FrameworkProblem0 p trs
  , InsertDPairs p trs
  , ExpandDPair  p trs
  )
type FrameworkProblemN    typ id = (FrameworkProblem    typ (NTRS id))
type FrameworkProblemNExt typ id = (FrameworkProblemExt typ (NTRS id))
type FrameworkProblemN0 typ id = (FrameworkProblem0 typ (NTRS id))
type FrameworkN    typ t v = FrameworkProblem    typ (NarradarTRS t v)
type FrameworkNExt typ t v = FrameworkProblemExt typ (NarradarTRS t v)

-- -------------------------
-- Constructing DP problems
-- -------------------------
type NarradarProblem typ t = Problem typ (NarradarTRS t Var)
type NProblem typ id = NarradarProblem typ (TermF id)

mkNewProblem x = mkNewProblemO nilObserver x

mkNewProblemO ::
    ( HasRules trs
    , Family.Rule trs ~ Rule (TermF id) Var
    , Family.Var(Family.Rule trs) ~ Family.Var trs
    , Ord id, NFData id
    , GetPairs typ
    , MkDPProblem typ (NTRS (DPIdentifier id))
    , RemovePrologId id, Pretty(DPIdentifier id)
    , Observable typ, Observable1 (Problem typ), Observable (DPIdentifier id)
    ) => Observer -> typ -> trs -> NProblem typ (DPIdentifier id)
mkNewProblemO (O o oo) typ trs = oo "mkDPProblem" mkDPProblemO typ (tRS rr') (tRS pairs) where
--   rr' :: [Rule (TermF (DPIdentifier id)) Var]
   rr'   = mapTermSymbols IdFunction <$$> rules trs
   pairs = getPairs typ rr'

-- -------------------------- --
-- Mapping over Problem types --
-- -------------------------- --
newtype Constant a (f :: * -> *) = Constant {getConstant :: a} deriving (Typeable, Generic)
instance Functor1 (Constant a) where fmap1 _ (Constant a) = Constant a
instance IsProblem typ => IsProblem (Constant typ a) where
  data Problem (Constant typ a) trs = ConstantP {getConstantP :: Problem typ trs} deriving (Generic)
  getFramework = Constant . getFramework . getConstantP
  getR = getR . getConstantP
instance IsDPProblem typ => IsDPProblem (Constant typ a) where
  getP = getP . getConstantP
instance MkProblem typ trs => MkProblem (Constant typ a) trs where
  mkProblem typ = ConstantP . mkProblem (getConstant typ)
  mapRO o f = ConstantP . mapRO o f . getConstantP
  setR_uncheckedO o x = ConstantP . setR_uncheckedO o x . getConstantP
instance MkDPProblem typ trs => MkDPProblem (Constant typ a) trs where
  mkDPProblemO o typ trs = ConstantP . mkDPProblemO o (getConstant typ) trs
  mapPO o f = ConstantP . mapPO o f . getConstantP
  setP_uncheckedO o x = ConstantP . setP_uncheckedO o x . getConstantP
instance ICap (Problem p trs) => ICap (Problem(Constant p a) trs) where
  icapO o p s = icapO o (getConstantP p) s
instance IUsableRules (Problem p trs) => IUsableRules (Problem (Constant p a) trs) where
  iUsableRulesM    p s = liftM ConstantP . iUsableRulesM    (getConstantP p) s
  iUsableRulesVarM p s = liftM ConstantP . iUsableRulesVarM (getConstantP p) s
instance NeededRules (Problem p trs) => NeededRules (Problem (Constant p a) trs) where
  neededRulesM p = liftM ConstantP . neededRulesM (getConstantP p)
instance HasMinimality typ => HasMinimality (Constant typ a) where
  getMinimality = getMinimality . getConstant
  setMinimality m = ConstantP . setMinimality m . getConstantP
instance ( Typeable a, ExpandDPair typ trs) => ExpandDPair (Constant typ a) trs where expandDPairO o p i = ConstantP . expandDPairO o (getConstantP p) i
instance (MkDPProblem typ trs, InsertDPairs typ trs) => InsertDPairs (Constant typ a) trs where insertDPairsO o p = ConstantP . insertDPairsO o (getConstantP p)
--instance Suitable info (Problem typ trs) => Suitable info (Problem (Constant typ a) trs)

instance Functor(Problem typ) => Functor (Problem(Constant typ a)) where
  fmap f = ConstantP . fmap f. getConstantP
instance Traversable (Problem typ) => Foldable (Problem (Constant typ a)) where
  foldMap f = foldMapDefault f
instance Traversable (Problem typ) => Traversable (Problem (Constant typ a)) where
  traverse f = fmap ConstantP . traverse f . getConstantP
instance Observable1 (Problem typ) => Observable1 (Problem (Constant typ a)) where
  observer1 p ctxt = ConstantP $ observer1 (getConstantP p) ctxt
instance NFData a => NFData (Constant a x) where rnf (Constant a) = rnf a
instance Pretty (Problem a trs) => Pretty (Problem(Constant a x) trs) where pPrint = pPrint . getConstantP
instance PprTPDB (Problem a trs) => PprTPDB (Problem(Constant a x) trs) where pprTPDB = pprTPDB . getConstantP
deriving instance Eq a => Eq (Constant a x)
deriving instance Eq (Problem typ trs) => Eq (Problem(Constant typ a) trs)
deriving instance Ord a => Ord (Constant a x)
deriving instance Ord (Problem typ trs) => Ord (Problem(Constant typ a) trs)
deriving instance Pretty a => Pretty(Constant a x)
deriving instance Observable a => Observable (Constant a f)
withPhantomProblemType f = mapFramework getConstant . f . mapFramework Constant

-- --------------------------------------
-- Comparing DP problems modulo variables
-- --------------------------------------

instance ( IsDPProblem a, Eq(EqModulo a)
         , HasRules trs
         , r ~ Family.Rule trs, GetFresh r, GetMatcher r, GetVars r
         , v ~ Family.Var r, Enum v, Rename v, Ord v, Observable v
         , t ~ Family.TermF r, Traversable t
         ) => Eq (EqModulo (Problem a trs)) where
  EqModulo pa == EqModulo pb =
    EqModulo (rules $ getR pa) == EqModulo (rules $ getR pb) &&
    EqModulo (rules $ getR pa) == EqModulo (rules $ getP pb) &&
    EqModulo (getFramework pa) == EqModulo (getFramework pb)

-- ---------------------------
-- Computing Dependency Pairs
-- ---------------------------
class GetPairs typ where
  getPairs :: ( HasRules trs, HasSignature trs
              , Rule t v ~ Family.Rule trs
              , t ~ f (DPIdentifier id)
              , Family.Id trs ~ DPIdentifier id
              , Family.Id (f (DPIdentifier id)) ~ DPIdentifier id
              , Ord id
              , Functor t, Foldable t, MapId f, HasId1 t
              ) => typ -> trs -> [Rule t v]

getPairsDefault ::
    ( HasRules trs, HasSignature trs
    , Rule (f id) v ~ Family.Rule trs
    , id ~ Family.Id trs
    , id ~ Family.Id (f id)
    , MapId f, HasId1 (f id)
    , Foldable (f id), Functor (f id)
    , DPSymbol id, Ord id
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

-- getEDG :: (Ord v, Enum v, Rename v
--           ,HasId t, Unify t
--           ,Ord (Term t v)
--           ,Pretty (Term t v), Pretty typ, Pretty v
--           ,MkDPProblem typ (NarradarTRS t v)
--           ,Traversable (Problem typ)
--           ,ICap (typ, NarradarTRS t v)
--           ,IUsableRules typ (NarradarTRS t v)
--           ) => Problem typ (NarradarTRS t v) -> G.Graph
-- getEDG p@(getP -> DPTRS _ _ gr _ _) = gr
-- getEDG p = filterSEDG p $ getdirectEDG p

-- getdirectEDG :: (Traversable (Problem typ)
--                 ,Enum v, Ord v, Pretty v, Rename v
--                 ,IsDPProblem typ, Unify t
--                 ,ICap (typ, NarradarTRS t v)
--                 ,Pretty (Term t v), Pretty typ
--                 ) => Problem typ (NarradarTRS t v) -> G.Graph
-- getdirectEDG p@(getP -> DPTRS dps _ _ (unif :!: _) _) =
--     assert (isValidUnif p) $
--     G.buildG (A.bounds dps) [ xy | (xy, Just _) <- A.assocs unif]

-- getDirectEDG p = G.buildG (0, length dps - 1) edges where
--   dps = rules $ getP p
--   edges = runIcap p $ runListT $ do
--                 (x, _ :-> r) <- liftL $ zip [0..] dps
--                 (y, l :-> _) <- liftL $ zip [0..] dps
--                 r' <- lift(getFresh r >>= icap p [])
--                 guard (unifies l r')
--                 return (x,y)
--   liftL = ListT . return

-- filterSEDG :: (Ord v, Enum v, Rename v
--               ,HasId t, Unify t
--               ,Ord (Term t v)
--               ,MkDPProblem typ (NarradarTRS t v)
--               ,Traversable (Problem typ)
--               ,ICap (typ, NarradarTRS t v)
--               ,IUsableRules typ (NarradarTRS t v)
--               ) => Problem typ (NarradarTRS t v) -> G.Graph -> G.Graph
-- filterSEDG p gr | isCollapsing (getP p) = gr
-- filterSEDG (getP -> dptrs@DPTRS{}) gr =
--     G.buildG (A.bounds gr)
--                [ (i,j) | (i,j) <- G.edges gr
--                        , isJust (dpUnifyInv dptrs j i)]

-- filterSEDG p gr = G.buildG (bounds gr) edges where
--   typ = getFramework p
--   dps = A.listArray (bounds gr) (rules $ getP p)
--   edges = runIcap p $ runListT $ do
--                 trs'   <- lift $ getFresh (rules $ getR p)
--                 let p' = setR (tRS trs') p
--                 (i, j) <- liftL (G.edges gr)
--                 let _ :-> r = safeAt "filterSEDG" dps i
--                     l :-> _ = safeAt "filterSEDG" dps j
--                 (getR -> trs_u) <- iUsableRulesMp p' [r]
--                 let trs_inv = swapRule <$> rules trs_u
--                 l'  <- lift (icap (typ, trs_inv) l)
--                 guard (unifies l' r)
--                 return (i,j)
--   liftL = ListT . return

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

instance (FrameworkN typ t v
         ,RemovePrologId(Family.Id t)
         ) =>
    ApplyAF (Problem typ (NarradarTRS t v))
  where
    apply af p = mkDPProblem typ trs' dps'
     where
       typ  = getFramework p
       trs' = apply af (getR p)
       dps' = apply af (getP p)
{-
instance (ApplyAF trs, IsDPProblem p) => ApplyAF (Problem p trs) where
    type AFId (Problem p trs) = AFId trs
    apply af = fmap (apply af)
-}
-- ------------------------------
-- Data.Term framework instances
-- ------------------------------

instance (v ~ Family.Var trs, Ord v, IsDPProblem typ, HasRules trs, Foldable (Problem typ)
         ) => HasRules (Problem typ trs) where rules = foldMap rules
instance (v ~ Family.Var trs, Ord v, GetFresh trs, Traversable (Problem typ)
         ) => GetFresh (Problem typ trs) where getFreshM = getFreshMdefault

instance (HasSignature trs
         ,HasSignature typ, IsDPProblem typ, Family.Id typ ~ Family.Id trs
         ) => HasSignature (Problem typ trs) where
  getSignature p = getSignature (getR p) `mappend`
                   getSignature (getP p) `mappend`
                   getSignature (getFramework p)

-- ------------------------------------
-- Dealing with the pairs in a problem
-- ------------------------------------

class (FrameworkProblem0 typ trs) => ExpandDPair typ trs where
  expandDPairO :: Observer -> Problem typ trs -> Int -> [RuleFor trs] -> Problem typ trs

expandDPair x = expandDPairO nilObserver x

expandDPairOdefault
            :: ( v ~ Var
               , FrameworkN typ t v
               ) =>
               Observer -> Problem typ (NarradarTRS t v) -> Int -> [Rule t v] -> Problem typ (NarradarTRS t v)

expandDPairOdefault
  (O o oo)
  p@(lowerNTRS.getP -> DPTRS typ dps rr gr (Two unif unifInv) _)
  i
  (filter (`notElem` elems dps) . snub -> newdps)
 = runIcap (rules p ++ newdps) $ do
    let dps'     = dps1 ++ dps2 ++ newdps
        l_dps'   = l_dps + l_newdps
        a_dps'   = A.listArray (0,l_dps') dps'
        mkUnif' arr arr' =
            A.array ((0,0), (l_dps', l_dps'))
                       ([((adjust x,adjust y), sigma) | ((x,y), sigma) <- assocs arr
                                                      , x /= i, y /= i] ++
                        concat [ [ (in1, safeAt "expandPair" arr' in1)
                                 , (in2, safeAt "expandPair" arr' in2)]
                               | j <- new_nodes
                               , k <- [0..l_dps']
                               , let in1 = (j,k)
                               , let in2 = (k,j)])
        adjust x = if x < i then x else x-1

    Two unif_new unifInv_new <- oo "compute unifiers" computeDPUnifiersO (setP (listTRS dps') p)
                                         -- The use of listTRS here is important ^^
    let unif'    = o "mkUnif" mkUnif' unif    unif_new
        unifInv' = mkUnif' unifInv unifInv_new
        dptrs'   = oo "dpTRS" dpTRSO' typ a_dps' rr (Two (o "unif'" unif') unifInv')
--      dptrs_new= dpTRS' a_dps' (unif_new :!: unifInv_new)

    let res = oo "setP" setPO dptrs' p

    assert (isValidUnif p) $
     assert (isValidUnif res) $
     return res

 where
   (dps1,_:dps2) = splitAt i (elems dps)
   new_nodes= [l_dps .. l_dps + l_newdps]
   l_dps    = assert (fst (bounds dps) == 0) $ snd (bounds dps)
   l_newdps = length newdps - 1

expandDPairOdefault (O o oo) p i newdps = o "expand pair fallthrough case" $ setP (tRS dps') p
  where
    dps'          = dps1 ++ dps2 ++ newdps
    (dps1,_:dps2) = splitAt i (rules $ getP p)


class MkDPProblem typ trs => InsertDPairs typ trs where
    insertDPairsO :: Observer -> Problem typ trs -> trs -> Problem typ trs
    insertDPairs  :: Problem typ trs -> trs -> Problem typ trs
    insertDPairs    = insertDPairsO nilObserver
    insertDPairsO _ = insertDPairs

insertDPairsDefault :: FrameworkProblemN0 typ id =>
                       Observer -> NProblem typ id -> NTRS id -> NProblem typ id
insertDPairsDefault o p newPairs = setP dps' p
  where
   dps' = --assert (Set.fromList(rules $ getR p) == rulesUsed (getP p)) $
          insertDPairs' o p (rules newPairs)

insertDPairs' ::
         (FrameworkProblemN0 typ id
         ) => Observer -> NProblem typ id -> [Rule (TermF id) Var] -> NTRS id
insertDPairs' o p@(lowerNTRS.getP -> DPTRS typ dps rr _ (Two unif unifInv) sig) newPairs
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

      Two unif_new unifInv_new <- computeDPUnifiersO o (setP (listTRS dps') p)
                               -- The use of listTRS here is important ^^
      let unif'    = mkUnif unif unif_new
          unifInv' = mkUnif unifInv unifInv_new

          dptrs'   = dpTRSO' o typ a_dps' rr (Two unif' unifInv')

      return dptrs'

-- -------------
-- Sanity Checks
-- -------------
isValidUnifO :: forall typ p id .
               ( FrameworkProblemN typ id

               ) => Observer -> NProblem typ id -> Bool
isValidUnifO o p@(lowerNTRS.getP -> DPTRS _ dps _ _ (Two unif _) _)
  | equivalent = True -- const True (pPrint (undefined :: Term t v))
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
  rr    = rules(getR p)
  (rules -> rr', unif') = runIcap (getP p) (getFresh (getR p) >>= \rr' -> (rr',) <$> computeDirectUnifiersO o (setR rr' p))

  validUnif = array ( (0,0), (l,l)) $ runIcap p $ runListT $ do
            (x, _ :-> r) <- liftL $ A.assocs dps
            (y, l :-> _) <- liftL $ A.assocs dps
            r' <- getFresh r >>= icap p []
            pprTrace (text "unify" <+> pPrint l <+> pPrint r') (return ())
            return ((x,y),unifies l r')

  valid = and $ zipWith (\subst unifies -> if unifies then isJust subst else isNothing subst) (elems unif) (elems validUnif)

  equivalent = (`all` indices unif) $ \i@(x,y) ->
                  case (unif!i,unif'!i) of
                    (Just _, Nothing) -> False
                    (Nothing, Just _) -> False
                    (Just (Two r1 l1), Just(Two r2 l2)) ->
                          applySubst r1 (rhs(rr !! x)) `equiv` applySubst r2 (rhs(rr'!!x)) &&
                          applySubst l1 (lhs(rr !! y)) `equiv` applySubst l2 (lhs(rr'!!y))
                    (Nothing, Nothing) -> True

isValidUnif _ = True


noDuplicateEdges gr = Set.size(Set.fromList (edges gr)) == length (edges gr)
