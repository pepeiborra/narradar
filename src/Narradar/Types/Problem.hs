{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE PatternGuards, RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}


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
import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable
import Data.Foldable as F (Foldable(..), toList)
import Data.Maybe (isJust)
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
import Narradar.Framework.Ppr
import Narradar.Utils
import Narradar.Types.Term hiding ((!))
import Narradar.Constraints.ICap
import Narradar.Constraints.UsableRules
import Narradar.Types.Var

import Data.Term.Rules

-- -------------------------
-- Constructing DP problems
-- -------------------------
type NarradarProblem typ t = Problem typ (NarradarTRS t Var)

mkNewProblem typ trs = mkDPProblem' typ  rr' (getPairs typ rr') where
   rr' = mapTermSymbols IdFunction <$$> rules trs

mkDerivedProblem typ p = mkDPProblem typ (getR p) (getP p)

mkDPProblem' :: ( v ~ Var
                , rr ~ [Rule t v]
                , ntrs ~ NarradarTRS t v
                , Unify t, HasId t, Ord (Term t v)
                , MkDPProblem typ (NarradarTRS t v), Traversable (Problem typ)
                , ICap t v (typ, ntrs)
                , IUsableRules t v (typ, ntrs)
                , Pretty (Term t v), Pretty typ
                ) => typ -> [Rule t v] -> [Rule t v] -> Problem typ (NarradarTRS t v)
mkDPProblem' typ rr dps = p where
      p     = mkDPProblem typ (tRS rr) dptrs
      dptrs = dpTRS typ rr dps (getEDG p)



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

getEDG p = filterSEDG p $ getdirectEDG p

getdirectEDG :: (Traversable (Problem typ)
                ,IsDPProblem typ, Enum v, Ord v, Unify t
                ,ICap t v (typ, NarradarTRS t v)
                ,Pretty v, Pretty (Term t v), Pretty typ
                ) => Problem typ (NarradarTRS t v) -> G.Graph
getdirectEDG p@(getP -> DPTRS dps _ (unif :!: _) _) =
    assert (isValidUnif p) $
    G.buildG (A.bounds dps) [ xy | (xy, Just _) <- A.assocs unif]

filterSEDG :: (IsDPProblem typ) => Problem typ (NarradarTRS t v) -> G.Graph -> G.Graph
filterSEDG (getP -> dptrs@DPTRS{}) gr =
    G.buildG (A.bounds gr)
               [ (i,j) | (i,j) <- G.edges gr
                       , isJust (dpUnifyInv dptrs j i)]

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

instance (IsDPProblem typ, HasSignature trs) => HasSignature (Problem typ trs) where
  type SignatureId (Problem typ trs) = SignatureId trs
  getSignature p = getSignature (getR p) `mappend` getSignature (getP p)

instance (Ord v, IsDPProblem typ, HasRules t v trs, Foldable (Problem typ)) => HasRules t v (Problem typ trs) where
    rules = foldMap rules

instance (Ord v, GetFresh t v trs, Traversable (Problem typ)) => GetFresh t v (Problem typ trs) where getFreshM = getFreshMdefault

instance (Ord v, GetVars v trs, Traversable (Problem typ)) => GetVars v (Problem typ trs) where getVars = foldMap getVars


-- ------------------------------------
-- Dealing with the pairs in a problem
-- ------------------------------------

expandDPair :: ( problem ~ Problem typ
               , HasId t, Foldable t, Unify t, Ord (Term t v), Ord v, Enum v
               , Traversable problem, IsDPProblem typ
               , ICap t v (typ, NarradarTRS t v)
               , IUsableRules t v (typ, NarradarTRS t v)
               , Pretty (Term t v), Pretty v, Pretty typ
               ) =>
               problem (NarradarTRS t v) -> Int -> [Rule t v] -> problem (NarradarTRS t v)
expandDPair p@(getP -> DPTRS dps gr (unif :!: unifInv) _) i (filter (`notElem` elems dps) . snub -> newdps)
 = assert (isValidUnif p) $
   assert (isValidUnif res) res
  where
   res = runIcap (rules p ++ newdps) $ do
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
        gr'      = buildG (0, l_dps')
                   ([(adjust x,adjust y) | (x,y) <- edges gr, x/=i, y/=i] ++
                    [(n,n') | n' <- new_nodes
                            , (n,m) <- edges gr, n/=i, m == i ] ++
                    [(n',n) | n <- gr ! i, n' <- new_nodes] ++
                    [(n',n'') | n' <- new_nodes, n'' <- new_nodes, i `elem` gr ! i])
        adjust x = if x < i then x else x-1

    unif_new :!: unifInv_new <- computeDPUnifiers (getProblemType p) (rules $ getR p) dps'
    let unif'    = mkUnif' unif    unif_new
        unifInv' = mkUnif' unifInv unifInv_new
        dptrs'   = dpTRS' a_dps' gr' (unif' :!: unifInv')
        dptrs_new= dpTRS' a_dps' gr' (unif_new :!: unifInv_new)
    return $ setP dptrs_new p

   (dps1,_:dps2) = splitAt i (elems dps)
   new_nodes= [l_dps .. l_dps + l_newdps]
   l_dps    = assert (fst (bounds dps) == 0) $ snd (bounds dps)
   l_newdps = length newdps - 1

expandDPair p i newdps = setP (tRS dps') p
  where
    dps'          = dps1 ++ dps2 ++ newdps
    (dps1,_:dps2) = splitAt i (rules $ getP p)

-- -------------
-- AF Problems
-- -------------
{-
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
--  withAF typ _ = error ("withAF - error: " ++ show(pPrint typ))
  stripGoal NarrowingModes{}  = Narrowing
  stripGoal BNarrowingModes{} = BNarrowing
  stripGoal GNarrowingModes{} = GNarrowing
  stripGoal LBNarrowingModes{}= LBNarrowing
  stripGoal m = m
--  withAF typ@Prolog{} _ =
-}

--instance (Ord id, Ord v) => ApplyAF (Problem id v) id where
--    apply pi p@Problem{trs,dps} = p{trs=apply pi trs, dps=apply pi dps}




{-
-- | Constructing NDP problems with as starting goal. This function takes an AF heuristic.
--   This is necessary so early because before splitting P into SCCs we need to ensure
--   that P is indeed a TRS (no extra variables).
--   I.e. we need to compute the filtering 'globally'
mkGoalProblem :: (Pretty id, Ord a, PolyHeuristicN heu id, Lattice (AF_ id), RemovePrologId a, id ~ Identifier a) =>
                 MkHeu heu -> ProblemType a -> NarradarTRS a Var -> [Problem id Var]
mkGoalProblem heu typ trs =
    let trs'       = convert trs
        dps        = mkDPs typ' trs'
        typ'       = typ{pi=extendedPi, goal=AF.extendToTupleSymbols (goal typ)}
        extendedPi = AF.extendToTupleSymbols (pi typ)
        p0         = mkProblem typ' trs' dps
        orProblems = case mkHeu heu p0 of
                       heu -> [assert (isSoundAF pi' p0) $
                               mkProblem typ'{pi=pi'} trs' dps
                                   | pi' <- Set.toList $ invariantEV heu (rules p0) extendedPi]
    in assert (not $ null orProblems) orProblems
-}

-- -------------
-- Utils
-- -------------

{-
mkDPSig (getSignature -> sig@Sig{definedSymbols}) =
  sig{definedSymbols = definedSymbols `mappend` Map.mapKeysMonotonic markDPSymbol definedSymbols}
-}

