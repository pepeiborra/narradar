{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module Narradar.Processor.GraphTransformation (
    RewritingP(..),
    NarrowingP(..),
    Instantiation(..),
    FInstantiation(..),
    GraphTransformationProof(..)
  ) where

import Control.Applicative
import Control.Monad.Identity (Identity(..))
import Control.Monad.Logic
import Data.Array.IArray hiding ((!), array)
import qualified Data.Array.IArray as A
import qualified Data.Graph as Gr
import Data.List (foldl1', isPrefixOf, nub)
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Text.XHtml (HTML)

import Narradar.Types hiding (narrowing, rewriting)
import Narradar.Types.TRS
import Narradar.Constraints.Syntactic
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Utils

import Data.Term.Rewriting
import Data.Term.Narrowing

import qualified Data.Term.Family as Family

data NarrowingP     (info :: * -> *) = NarrowingP
data Instantiation  (info :: * -> *) = Instantiation
data FInstantiation (info :: * -> *) = FInstantiation
data RewritingP     (info :: * -> *) = RewritingP

type instance InfoConstraint (NarrowingP info) = info
type instance InfoConstraint (RewritingP info) = info
type instance InfoConstraint (Instantiation info) = info
type instance InfoConstraint (FInstantiation info) = info

-- * Narrowing
-- ------------

instance ( t ~ f (DPIdentifier id)
         , Ord (Term t Var), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier id
         , IUsableRules Rewriting (NarradarTRS t Var)
         , Info info GraphTransformationProof
         ) =>
  Processor (NarrowingP info) (NarradarProblem Rewriting t) where
  type Typ (NarrowingP info) (NarradarProblem Rewriting t) = Rewriting
  type Trs (NarrowingP info) (NarradarProblem Rewriting t) = NarradarTRS t Var
  applySearch NarrowingP = narrowing

instance ( t ~ f (DPIdentifier id)
         , Ord (Term t Var), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier id
         , IUsableRules IRewriting (NarradarTRS t Var)
         , Info info GraphTransformationProof
         ) =>
  Processor (NarrowingP info) (NarradarProblem IRewriting t) where
  type Typ (NarrowingP info) (NarradarProblem IRewriting t) = IRewriting
  type Trs (NarrowingP info) (NarradarProblem IRewriting t) = NarradarTRS t Var
  applySearch NarrowingP = narrowing_innermost

-- Liftings

instance (Processor (NarrowingP info) (Problem b trs)
         ,Info info (Problem b trs)
         ,Problem b trs ~ Res (NarrowingP info) (Problem b trs)
         ) =>
  Processor (NarrowingP info) (Problem (MkNarrowing b) trs) where
  type Typ (NarrowingP info) (Problem (MkNarrowing b) trs) = MkNarrowing b
  type Trs (NarrowingP info) (Problem (MkNarrowing b) trs) = trs
  applySearch = liftProcessorS

instance (Processor (NarrowingP info) (Problem b trs)
         ,Info info (Problem b trs)
         ,Problem b trs ~ Res (NarrowingP info) (Problem b trs)
         ) =>
  Processor (NarrowingP info) (Problem (MkNarrowingGen b) trs) where
  type Typ (NarrowingP info) (Problem (MkNarrowingGen b) trs) = MkNarrowingGen b
  type Trs (NarrowingP info) (Problem (MkNarrowingGen b) trs) = trs
  applySearch = liftProcessorS

-- Not so straightforward liftings

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t Rewriting) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t Rewriting) t) = InitialGoal t Rewriting
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t Rewriting) t) = NarradarTRS t Var
   applySearch tag = narrowingIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t IRewriting) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t IRewriting) t) = InitialGoal t IRewriting
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t IRewriting) t) = NarradarTRS t Var
   applySearch tag = narrowing_innermostIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , MkDPProblem (InitialGoal t Narrowing) (NarradarTRS t Var)
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t Narrowing) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t Narrowing) t) = InitialGoal t Narrowing
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t Narrowing) t) = NarradarTRS t Var
   applySearch tag = narrowingIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         , MkDPProblem (InitialGoal t CNarrowing) (NarradarTRS t Var)
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowing) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowing) t) = InitialGoal t CNarrowing
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowing) t) = NarradarTRS t Var
   applySearch tag = narrowing_innermostIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier (GenId id)
         , t ~ f (DPIdentifier (GenId id)), MapId f
         , MkDPProblem NarrowingGen (NarradarTRS t Var)
         , MkDPProblem (InitialGoal t NarrowingGen) (NarradarTRS t Var)
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t NarrowingGen) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t NarrowingGen) t) = InitialGoal t NarrowingGen
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t NarrowingGen) t) = NarradarTRS t Var
   applySearch tag = narrowingIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, Family.Id t ~ DPIdentifier (GenId id)
         , t ~ f (DPIdentifier (GenId id)), MapId f
         , MkDPProblem CNarrowingGen (NarradarTRS t Var)
         , MkDPProblem (InitialGoal t CNarrowingGen) (NarradarTRS t Var)
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowingGen) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowingGen) t) = InitialGoal t CNarrowingGen
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowingGen) t) = NarradarTRS t Var
   applySearch tag = narrowing_innermostIG

-- * Instantiation
-- ---------------

instance (trs ~ NarradarTRS t Var
         ,t ~ f(DPIdentifier id), MapId f
         ,DPIdentifier id ~ Family.Id t, HasId t
         ,Unify t, Pretty (t(Term t Var)), Ord (Term t Var)
         ,Info info GraphTransformationProof, Pretty (MkRewriting st)
         ,MkDPProblem (MkRewriting st) (NarradarTRS t Var)
         ,ICap (MkRewriting st, NarradarTRS t Var)
         ,IUsableRules (MkRewriting st) (NarradarTRS t Var)
         ) =>
    Processor (Instantiation info) (NarradarProblem (MkRewriting st) t) where
  type Typ (Instantiation info) (NarradarProblem (MkRewriting st) t) = MkRewriting st
  type Trs (Instantiation info) (NarradarProblem (MkRewriting st) t) = NarradarTRS t Var
  applySearch Instantiation = instantiation

instance (Info info (NarradarProblem b t)
         ,Processor (Instantiation info) (NarradarProblem b t)
         ,NarradarProblem b t ~ Res (Instantiation info) (NarradarProblem b t)
         ) =>
    Processor (Instantiation info) (NarradarProblem (MkNarrowing b) t) where
  type Typ (Instantiation info) (NarradarProblem (MkNarrowing b) t) = MkNarrowing b
  type Trs (Instantiation info) (NarradarProblem (MkNarrowing b) t) = NarradarTRS t Var
  applySearch = liftProcessorS

instance (trs ~ NarradarTRS t v
         ,v   ~ Var
         ,t   ~ f id
         ,id  ~ Family.Id t, HasId t, MapId f, DPSymbol id
         ,Unify t, Pretty (t(Term t Var)), Pretty typ, Ord (t(Term t Var))
         ,MkDPProblem typ trs
         ,MkDPProblem (InitialGoal t typ) trs
         ,Traversable (Problem typ)
         ,IUsableRules typ (NarradarTRS t v)
         ,NeededRules  typ (NarradarTRS t v)
         ,ICap (typ, trs)
         ,Info info GraphTransformationProof
         ) =>
    Processor (Instantiation info) (NarradarProblem (InitialGoal (f id) typ) (f id))
 where
  type Typ (Instantiation info) (NarradarProblem (InitialGoal (f id) typ) (f id)) = InitialGoal (f id) typ
  type Trs (Instantiation info) (NarradarProblem (InitialGoal (f id) typ) (f id)) = NarradarTRS (f id) Var
  applySearch Instantiation p@InitialGoalProblem{dgraph}
   | not $ isDPTRS (getP p) = error "instantiationProcessor: expected a problem carrying a DPTRS"
   | otherwise = [ singleP (InstantiationProof olddp newdps) p0 p1
                     | (i,olddp, newdps) <- dpss
                     , let p0 = expandDPair p i newdps
                     , let p1 = expandDGraph p0 olddp newdps
                 ]

   where currentPairs = [0..] `zip` tag (fromMaybe err . (`lookupNode` dgraph)) (rules$ getP p)
         dpss         = [ (i, olddp, newdps)
                              | (i,(j,olddp)) <-currentPairs
                              , let newdps = f j olddp
                              , not (null newdps)]
         err = error "Instantiation processor: unexpected"

         f :: Int -> Rule t v -> [Rule t v]
         f  i olddp@(s :-> t)
                  | EqModulo olddp `notElem` (EqModulo <$> newdps) = newdps
                  | otherwise = []
            where
              allPairs = pairs dgraph
              gr       = fullgraph dgraph
              newdps   = [ applySubst sigma s :-> applySubst sigma t
                          | Just sigma <- snub [dpUnify allPairs i m | (m,n) <- Gr.edges gr, n == i]
                         ]


-- * Forward Instantiation
-- -----------------------

instance (trs ~ NarradarTRS t Var
         ,t ~ f (DPIdentifier id), MapId f
         ,DPIdentifier id ~ Family.Id t, HasId t
         ,Unify t, Pretty (Term t Var), Ord (Term t Var)
         ,Info info GraphTransformationProof
         ,Pretty (MkRewriting st)
         ,MkDPProblem (MkRewriting st) (NarradarTRS t Var)
         ,MkDPProblem (InitialGoal t (MkRewriting st)) trs
         ,ICap (MkRewriting st, NarradarTRS t Var)
         ,IUsableRules (MkRewriting st) (NarradarTRS t Var)
         ) =>
    Processor (FInstantiation info) (NarradarProblem (MkRewriting st) t) where
  type Typ (FInstantiation info) (NarradarProblem (MkRewriting st) t) = MkRewriting st
  type Trs (FInstantiation info) (NarradarProblem (MkRewriting st) t) = NarradarTRS t Var
  applySearch FInstantiation = finstantiation

instance (Info info (NarradarProblem b t)
         ,Processor (FInstantiation info) (NarradarProblem b t)
         ,NarradarProblem b t ~ Res (FInstantiation info) (NarradarProblem b t)
         ) =>
 Processor (FInstantiation info) (NarradarProblem (MkNarrowing b) t) where
 type Typ (FInstantiation info) (NarradarProblem (MkNarrowing b) t) = MkNarrowing b
 type Trs (FInstantiation info) (NarradarProblem (MkNarrowing b) t) = NarradarTRS t Var
 applySearch = liftProcessorS

instance (v ~ Var
         ,t ~ f (DPIdentifier id), MapId f
         ,Family.Id t ~ DPIdentifier id, HasId t, Unify t
         ,Pretty typ
         ,MkDPProblem  typ (NarradarTRS t Var)
         ,MkDPProblem (InitialGoal t typ) (NarradarTRS t Var)
         ,Traversable (Problem typ)
         ,Pretty (t(Term t v)), Ord(t(Term t v))
         ,IUsableRules typ (NarradarTRS t v)
         ,NeededRules  typ (NarradarTRS t v)
         ,ICap (typ, (NarradarTRS t Var))
         ,Info info GraphTransformationProof
         ) =>
    Processor (FInstantiation info) (NarradarProblem (InitialGoal t typ) t)
 where
 type Typ (FInstantiation info) (NarradarProblem (InitialGoal t typ) t) = InitialGoal t typ
 type Trs (FInstantiation info) (NarradarProblem (InitialGoal t typ) t) = NarradarTRS t Var
 applySearch FInstantiation p@InitialGoalProblem{dgraph}
  | not $ isDPTRS (getP p) = error "finstantiationProcessor: expected a problem carrying a DPTRS"
  | isCollapsing (getR p)  = mzero  -- no point in instantiating everything around
  | otherwise = [ singleP (FInstantiationProof olddp newdps) p p'
                     | (i, olddp, newdps) <- dpss
                     , let p' = expandDGraph (expandDPair p i newdps) olddp newdps
                ]
   where currentPairs = [0..] `zip` tag (fromMaybe err . (`lookupNode` dgraph)) (rules$ getP p)
         dpss = [ (i, olddp, newdps)
                              | (i,(j,olddp)) <-currentPairs
                              , let newdps = f j olddp
                              , not (null newdps)]
         err = error "F Instantiation processor: unexpected"

         f i olddp@(s :-> t)
                  | EqModulo olddp `notElem` (EqModulo <$> newdps) = newdps
                  | otherwise = []
              where
                gr       = fullgraph dgraph
                allPairs = pairs dgraph
                newdps    = [applySubst sigma s :-> applySubst sigma t
                             | Just sigma <- snub [dpUnifyInv allPairs j i
                                                       | j <- safeAt "FInstantiation" gr i]]

-- * Rewriting
-- ------------

instance ( t ~ f id, v ~ Var
         , HasId t, Unify t
         , Pretty (t(Term t v)), Ord (t(Term t v))
         , Info info GraphTransformationProof
         ) =>
    Processor (RewritingP info) (NarradarProblem IRewriting t)
 where
  type Typ (RewritingP info) (NarradarProblem IRewriting t) = IRewriting
  type Trs (RewritingP info) (NarradarProblem IRewriting t) = NarradarTRS t Var
  applySearch RewritingP = rewritingI

instance ( t ~ f id, v ~ Var
         , HasId t, Unify t, MapId f
         , DPSymbol id
         , Pretty (t(Term t v)), Ord (t(Term t v))
         , Info info GraphTransformationProof
         ) =>
    Processor (RewritingP info) (NarradarProblem (InitialGoal t IRewriting) t)
 where
  type Typ (RewritingP info) (NarradarProblem (InitialGoal t IRewriting) t) = InitialGoal t IRewriting
  type Trs (RewritingP info) (NarradarProblem (InitialGoal t IRewriting) t) = NarradarTRS t Var
  applySearch RewritingP = rewritingGoalI


-- -------
-- Proofs
-- -------

data GraphTransformationProof where
    NarrowingProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> [Rule t v]          -- ^ New pairs
                   -> GraphTransformationProof
    InstantiationProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> [Rule t v]          -- ^ New pairs
                   -> GraphTransformationProof
    FInstantiationProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> [Rule t v]          -- ^ New pairs
                   -> GraphTransformationProof
    RewritingProof :: Pretty (Rule t v) =>
                      Rule t v            -- ^ Old pair
                   -> Rule t v            -- ^ New pair
                   -> GraphTransformationProof
    RewritingFail :: GraphTransformationProof

instance Pretty GraphTransformationProof where
  pPrint (NarrowingProof old new) =
                                 text "Narrowing Processor." $+$
                                 text "Pair" <+> pPrint old <+> text "replaced by" $$ pPrint new

  pPrint (InstantiationProof old new) =
                                 text "Instantiation Processor." <+>
                                 text "Pair" <+> pPrint old <+> text "replaced by" $$ pPrint new

  pPrint (FInstantiationProof old new) =
                                 text "FInstantiation Processor." $$
                                 text "Pair" <+> pPrint old <+> text "replaced by" $$ pPrint new

  pPrint (RewritingProof old new) =
                                 text "Rewriting Processor." $$
                                 text "Pair" <+> pPrint old <+> text "replaced by" $$ pPrint new

  pPrint RewritingFail = text "Failed to apply the Rewriting refinement processor"
-- ----------------
-- Implementation
-- ----------------
-- Narrowing

narrowing, narrowing_innermost
          :: (p  ~ Problem typ trs
             ,trs ~ NarradarTRS t v
             ,v ~ Var
             ,Family.Id t  ~ DPIdentifier id, HasId t, Unify t
             ,Enum v, GetVars v, Ord (Term t v)
             ,MkDPProblem typ trs, Traversable (Problem typ)
             ,IUsableRules typ trs, ICap (typ,trs)
             ,Pretty (t(Term t v)), Pretty v, Pretty typ
             ,Info info p
             ,Info info GraphTransformationProof
             ,Monad mp
             ) =>
             Problem typ trs -> [Proof info mp (Problem typ trs)]

narrowing p0
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise  = [ singleP (NarrowingProof olddp newdps) p0 (expandDPair p0 i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = safeAt "narrowing" dpsA i
                     , let newdps = dps' !! i]
    where
          (dpsA, gr) = (rulesArray (getP p0), rulesGraph (getP p0))
          dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                          , all (not.null) dps]
          f (i, olddp@(_s :-> t))
              | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
              | otherwise = []
           where
             newdps
              | isLinear t
              , isNothing (unify' (getVariant t uu) `mapM` uu)
              , new_dps <- [(i,dp')
                              | (dp',p) <- narrow1DP (rules $ getR p0) olddp
                              , let validPos
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0)))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs.snd) new_dps then [] else new_dps

              | otherwise = []
               where uu     = map (lhs . (safeAt "narrowing" dpsA)) (safeAt "narrowing" gr i)
                     pos_uu = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)

narrowing_innermost p0
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (NarrowingProof olddp newdps) p0 (expandDPair p0 i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = safeAt "narrowing_innermost" dpsA i
                     , let newdps = dps' !! i]
    where --  dpss = snd <$$> (map concat $ filter (all (not.null)) $ maps f (assocs dpsA))
          (dpsA, gr) = (rulesArray (getP p0), rulesGraph (getP p0))
          dpss = snub [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                          , all (not.null) dps]
          f (i, olddp@(_s :-> t))
              | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
              | otherwise = []
           where
             newdps
              | isNothing (unify' (getVariant t uu) `mapM` uu)
              , new_dps <- [(i,dp')
                              | (dp',p) <- narrow1DP (rules $ getR p0) olddp
                              , let validPos
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0)))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs.snd) new_dps then [] else new_dps

              | otherwise = []
               where uu     = map (lhs . (safeAt "narrowing_innermost" dpsA)) (safeAt "narrowing_innermost" gr i)
                     pos_uu = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)
narrowingIG, narrowing_innermostIG
          :: (trs ~ NarradarTRS t v
             ,t ~ f (DPIdentifier id), MapId f
             ,v ~ Var
             ,Family.Id t  ~ DPIdentifier id, HasId t, Unify t
             ,Enum v, GetVars v, Ord (t(Term t v))
             ,MkDPProblem (InitialGoal t typ) trs
             ,MkDPProblem typ trs
             ,Traversable (Problem typ)
             ,IUsableRules typ (NarradarTRS t v)
             ,NeededRules  typ (NarradarTRS t v)
             ,ICap (typ,trs)
             ,Pretty (t(Term t v)), Pretty v, Pretty typ
             ,Info info (Problem (InitialGoal t typ) trs)
             ,Info info GraphTransformationProof
             ,Monad mp
             ) =>
             Problem (InitialGoal t typ) trs -> [Proof info mp (Problem (InitialGoal t typ) trs)]
narrowingIG p0@InitialGoalProblem{dgraph}
  | not $ isDPTRS (getP p0) = error "narrowingIG Processor: expected a problem carrying a DPTRS"
  | otherwise  = [ singleP (NarrowingProof olddp newdps) p0 p'
                     | (i, olddp, newdps) <- dpss
                     , let p' = expandDGraph (expandDPair p0 i newdps) olddp newdps]
    where
          allPairs     = rulesArray $ pairs dgraph
          currentPairs = [0..] `zip` tag (fromMaybe err . (`lookupNode` dgraph)) (rules$ getP p0)
          dpss = [ (i,olddp, newdps)
                            | (i,(j, olddp))  <- currentPairs
                            , Just newdps <- [f j olddp] ]

          err = error "narrowing (IG) processor: unexpected"

          f i olddp@(_s :-> t)
              | not (null newdps)
              , EqModulo olddp `notElem` (EqModulo <$> newdps) = Just newdps

              | otherwise = Nothing
           where
             newdps
              | isLinear t
              , isNothing (unify' (getVariant t uu) `mapM` uu)
              , new_dps <- [ dp'
                              | (dp',p) <- narrow1DP (rules $ getR p0) olddp
                              , let validPos
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0)))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs) new_dps then [] else new_dps

              | otherwise = []
               where
                 gr       = fullgraph dgraph
                 uu       = map (lhs . (safeAt "narrowingIG" allPairs))
                                (safeAt "narrowingIG" gr i)
                 pos_uu   = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)

narrowing_innermostIG p0@InitialGoalProblem{dgraph}
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (NarrowingProof olddp newdps) p0 p'
                     | (i, olddp, newdps) <- dpss
                     , let p' = expandDGraph (expandDPair p0 i newdps) olddp newdps]
    where
          allPairs     = rulesArray $ pairs dgraph
          currentPairs = [0..] `zip` tag (fromMaybe err . (`lookupNode` dgraph)) (rules$ getP p0)
          dpss = [ (i,olddp, newdps) | (i,(j, olddp)) <- currentPairs, Just newdps <- [f j olddp]]

          err = error "narrowing innermost (IG) processor: unexpected"

          f i olddp@(_s :-> t)
              | not (null newdps)
              , EqModulo olddp `notElem` (EqModulo <$> newdps) = Just newdps

              | otherwise = Nothing
           where
             newdps
              | isNothing (unify' (getVariant t uu) `mapM` uu)
              , new_dps <- [dp'
                              | (dp',p) <- narrow1DP (rules $ getR p0) olddp
                              , let validPos
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0)))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs) new_dps then [] else new_dps

              | otherwise = []
               where
                 gr       = fullgraph dgraph
                 uu       = map (lhs . (safeAt "narrowing_innermostIG" allPairs))
                                (safeAt "narrowing_innermostIG" gr i)
                 pos_uu   = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)

narrow1DP rr (l :-> r) = [ (applySubst theta l :-> r', p)
                           | ((r',p),theta) <- observeAll (narrow1P rr r) ]

-- Instantiation

instantiation, finstantiation
          :: forall typ trs mp t f v p id info.
             (p  ~ Problem typ trs, Info info p
             ,trs ~ NarradarTRS t v
             ,v ~ Var
             ,t ~ f (DPIdentifier id)
             ,Family.Id t ~ DPIdentifier id, HasId t, Unify t
             ,Enum v, GetVars v
             ,MkDPProblem typ trs, Traversable (Problem typ)
             ,Pretty ((Term t v)), Ord(Term t v), Pretty v, Pretty typ
             ,IUsableRules typ (NarradarTRS t v), ICap (typ, trs)
             ,Info info GraphTransformationProof
             ,Monad mp
             ) =>
             Problem typ trs -> [Proof info mp (Problem typ trs)]

instantiation p
  | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
  | not $ isDPTRS (getP p) = error "instantiationProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (InstantiationProof olddp newdps) p (expandDPair p i newdps)
                     | (i,dps') <- dpss
                     , let olddp  = safeAt "instantiation" dpsA i
                     , let newdps = dps' !! i ]

   where (dpsA, gr) = (rulesArray (getP p), rulesGraph (getP p))
         dps  = elems dpsA
         dpss = [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                    , all (not.null) dps]
         f :: (Int, Rule t v) -> [(Int, Rule t v)]
         f  (i,olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
            where newdps = [ (i, applySubst sigma s :-> applySubst sigma t)
                            | Just sigma <- snub [dpUnify (getP p) i m | (m,n) <- Gr.edges gr, n == i]]

--instantiation p = [return p]

-- Forward instantiation

finstantiation p
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | not $ isDPTRS (getP p) = error "finstantiationProcessor: expected a problem carrying a DPTRS"
  | isCollapsing (getR p) = mzero
  | otherwise = [ singleP (FInstantiationProof olddp newdps) p
                           (expandDPair p i newdps)
                     | (i, dps') <- dpss
                     , let olddp  = safeAt "finstantiation" dpsA  i
                     , let newdps = dps' !! i]
   where (dpsA, gr) = (rulesArray (getP p), rulesGraph (getP p))
         dps  = elems dpsA
         dpss = [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps f (assocs dpsA))
                                    , all (not.null) dps]
         f :: (Int, Rule t v) -> [(Int, Rule t v)]
         f (i, olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
              where newdps = [(i, applySubst sigma s :-> applySubst sigma t)
                             | Just sigma <- snub [dpUnifyInv (getP p) j i | j <- safeAt "finstantiation" gr i]]
-- finstantiation p = [return p]


-- I should teach myself about comonads
-- http://sigfpe.blogspot.com/2008/03/comonadic-arrays.html
-- ---------------------------------------------------------

maps, maps' :: Monad m => (a -> m a) -> [a] -> [[m a]]
maps f xx = concat $ elems $ array (Pointer 1 (listArray (1, length xx) xx) =>> appF) where
    appF (Pointer i a) = let a' = amap return a in  map elems [a' // [(i, f(safeAt "maps" a i))] ]

maps' f xx = [ updateAt i xx | i <- [0..length xx - 1]] where
  updateAt 0 (x:rest) = f x      : map return rest
  updateAt i (x:xx)   = return x : updateAt (i-1) xx

-- maps and maps' are equivalent
propMaps f xx = maps f xx == maps' f xx where _types = (xx :: [Bool], f :: Bool -> [Bool])


-- rewriting

rewriting p0
    | [p] <- problems = p
    | otherwise = dontKnow RewritingFail p0
    where
     redexes t = [ p | p <- positions t, isJust (rewrite1 (rules $ getR p0) t)]

     problems = [ singleP (RewritingProof olddp (s:->t')) p0 (expandDPair p0 i [s:->t'])
                | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
                , [p] <- [redexes t]
                , let urp = iUsableRules p0 [t!p]
                , isNonOverlapping urp
                , [t'] <- [rewrite1p (rules urp) t p]
                ]
rewritingI p0
    | otherwise     = problems
    where
     redexes t = [ p | p <- positions t, isJust (rewrite1 (rules $ getR p0) t)]

     problems = [ singleP (RewritingProof olddp (s:->t')) p0 (expandDPair p0 i [s:->t'])
                | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
                , p <- redexes t
                , let urp = iUsableRules p0 [t!p]
                , isNonOverlapping urp
                , [t'] <- [rewrite1p (rules urp) t p]
                ]

rewritingGoal p0
    | [x] <- problem = x
    | otherwise = dontKnow RewritingFail p0
   where
    problem = [ singleP (RewritingProof olddp newdp) p0 p'
                | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
                , [p] <- [redexes t]
                , let urp = iUsableRules p0 [t!p]
                , isNonOverlapping urp
                , [t'] <- [rewrite1 (rules urp) t]
                , let newdp = s:->t'
                      p' = expandDGraph (expandDPair p0 i [newdp]) olddp [newdp]
                ]
    redexes t = [ p | p <- positions t, isJust (rewrite1 (rules $ getR p0) t)]

rewritingGoalI p0
    | otherwise = problems
   where
    problems = [ singleP (RewritingProof olddp newdp) p0 p'
               | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
               , p <- redexes t
               , let urp = iUsableRules p0 [t!p]
               , isNonOverlapping urp
               , [t'] <- [rewrite1p (rules urp) t p]
               , let newdp = s:->t'
                     p' = expandDGraph (expandDPair p0 i [newdp]) olddp [newdp]
               ]
    redexes t = [ p | p <- positions t, isJust (rewrite1 (rules $ getR p0) t)]

-- ------------------------------
-- Extracted from category-extras
-- ------------------------------
data Pointer i a = Pointer { index :: i, array :: Array i a } deriving (Show,Read)

instance Ix i => Functor (Pointer i) where
    fmap f (Pointer i a) = Pointer i (fmap f a)

instance Ix i => Copointed (Pointer i) where
    extract (Pointer i a) = safeAt "Copointed Pointer" a i

instance Ix i => Comonad (Pointer i) where
    extend f (Pointer i a) = Pointer i . listArray bds $ fmap (f . flip Pointer a) (range bds) where
                                     bds = bounds a


class Copointed w => Comonad w where
        duplicate :: w a -> w (w a)
        extend :: (w a -> b) -> w a -> w b
        extend f = fmap f . duplicate
        duplicate = extend id

-- | 'extend' with the arguments swapped. Dual to '>>=' for monads.
(=>>) :: Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

class Functor f => Copointed f where
        extract :: f a -> a -- Algebra f a

instance Copointed Identity where
        extract = runIdentity

instance Copointed ((,)e) where
    extract = snd
