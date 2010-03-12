{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module Narradar.Processor.GraphTransformation (NarrowingP(..), Instantiation(..), FInstantiation(..), GraphTransformationProof(..)) where

import Control.Applicative
import Control.Monad.Identity (Identity(..))
import Control.Monad.Logic
import Data.Array.IArray hiding ( array )
import qualified Data.Array.IArray as A
import qualified Data.Graph as Gr
import Data.List (foldl1', isPrefixOf, nub)
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Text.XHtml (HTML)

import Narradar.Types hiding ((!), narrowing)
import Narradar.Types.TRS
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Utils

import Data.Term.Narrowing


data NarrowingP     = NarrowingP
data Instantiation  = Instantiation
data FInstantiation = FInstantiation

-- * Narrowing

instance ( t ~ f (DPIdentifier id)
         , Ord (Term t Var), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier id
         , IUsableRules t Var Rewriting (NarradarTRS t Var)
         , Info info GraphTransformationProof
         ) =>
    Processor info NarrowingP (NarradarProblem Rewriting t) (NarradarProblem Rewriting t) where
  applySearch NarrowingP = narrowing

instance ( t ~ f (DPIdentifier id)
         , Ord (Term t Var), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier id
         , IUsableRules t Var IRewriting (NarradarTRS t Var)
         , Info info GraphTransformationProof
         ) =>
    Processor info NarrowingP (NarradarProblem IRewriting t) (NarradarProblem IRewriting t) where
  applySearch NarrowingP = narrowing_innermost

-- Liftings

instance (Processor info NarrowingP (Problem b trs) (Problem b trs)
         ,Info info (Problem b trs)
         ) =>
    Processor info NarrowingP (Problem (MkNarrowing b) trs) (Problem (MkNarrowing b) trs) where
  applySearch = liftProcessorS

instance (Processor info NarrowingP (Problem b trs) (Problem b trs)
         ,Info info (Problem b trs)
         ) =>
    Processor info NarrowingP (Problem (MkNarrowingGen b) trs) (Problem (MkNarrowingGen b) trs) where
  applySearch = liftProcessorS

-- Not so straightforward liftings

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         )=> Processor info NarrowingP (NarradarProblem (InitialGoal t Rewriting) t) (NarradarProblem (InitialGoal t Rewriting) t)
  where
   applySearch tag = narrowingIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         )=> Processor info NarrowingP (NarradarProblem (InitialGoal t IRewriting) t) (NarradarProblem (InitialGoal t IRewriting) t)
  where
   applySearch tag = narrowing_innermostIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         )=> Processor info NarrowingP (NarradarProblem (InitialGoal t Narrowing) t) (NarradarProblem (InitialGoal t Narrowing) t)
  where
   applySearch tag = narrowingIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Info info GraphTransformationProof
         )=> Processor info NarrowingP (NarradarProblem (InitialGoal t CNarrowing) t) (NarradarProblem (InitialGoal t CNarrowing) t)
  where
   applySearch tag = narrowing_innermostIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier (GenId id)
         , t ~ f (DPIdentifier (GenId id)), MapId f
         , MkDPProblem NarrowingGen (NarradarTRS t Var)
         , Info info GraphTransformationProof
         )=> Processor info NarrowingP (NarradarProblem (InitialGoal t NarrowingGen) t) (NarradarProblem (InitialGoal t NarrowingGen) t)
  where
   applySearch tag = narrowingIG

instance ( Ord (t(Term t Var)), Pretty (t(Term t Var)), Unify t, HasId t, TermId t ~ DPIdentifier (GenId id)
         , t ~ f (DPIdentifier (GenId id)), MapId f
         , MkDPProblem CNarrowingGen (NarradarTRS t Var)
         , Info info GraphTransformationProof
         )=> Processor info NarrowingP (NarradarProblem (InitialGoal t CNarrowingGen) t) (NarradarProblem (InitialGoal t CNarrowingGen) t)
  where
   applySearch tag = narrowing_innermostIG

-- * Instantiation

instance (trs ~ NarradarTRS t Var
         ,t ~ f(DPIdentifier id), MapId f
         ,DPIdentifier id ~ TermId t, HasId t
         ,Unify t, Pretty (t(Term t Var)), Ord (Term t Var)
         ,Info info GraphTransformationProof, Pretty (MkRewriting st)
         ,MkDPProblem (MkRewriting st) (NarradarTRS t Var)
         ,ICap t Var (MkRewriting st, NarradarTRS t Var)
         ,IUsableRules t Var (MkRewriting st) (NarradarTRS t Var)
         ) =>
    Processor info Instantiation (NarradarProblem (MkRewriting st) t) (NarradarProblem (MkRewriting st) t) where
  applySearch Instantiation = instantiation

instance (Info info (NarradarProblem b t)
         ,Processor info Instantiation (NarradarProblem b t) (NarradarProblem b t)
         ) =>
    Processor info Instantiation (NarradarProblem (MkNarrowing b) t) (NarradarProblem (MkNarrowing b) t) where
  applySearch = liftProcessorS

instance (trs ~ NarradarTRS t v
         ,v   ~ Var
         ,t   ~ f id
         ,id  ~ TermId t, HasId t, MapId f, DPSymbol id
         ,Unify t, Pretty (t(Term t Var)), Pretty typ, Ord (t(Term t Var))
         ,MkDPProblem typ trs, Traversable (Problem typ)
         ,IUsableRules t v typ (NarradarTRS t v)
         ,IUsableRules t v typ trs
         ,ICap t v (typ, trs)
         ,Info info GraphTransformationProof
         ) =>
    Processor info Instantiation (NarradarProblem (InitialGoal (f id) typ) (f id))
                                 (NarradarProblem (InitialGoal (f id) typ) (f id))
 where
  applySearch Instantiation p@InitialGoalProblem{..}
   | null currentPairs      = [return p]
   | not $ isDPTRS (getP p) = error "instantiationProcessor: expected a problem carrying a DPTRS"
   | otherwise = [ singleP (InstantiationProof olddp newdps) p
                             (mkDerivedDPProblem typ' p')
                     | (i,olddp, newdps) <- dpss
                     , let dgraph' = expandDGraph p olddp newdps
                     , let typ' = InitialGoal goals (Just dgraph') (getProblemType baseProblem)
                     , let p'   = expandDPair (getBaseProblem p) i newdps
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

instance (trs ~ NarradarTRS t Var
         ,t ~ f (DPIdentifier id), MapId f
         ,DPIdentifier id ~ TermId t, HasId t
         ,Unify t, Pretty (Term t Var), Ord (Term t Var)
         ,Info info GraphTransformationProof, Pretty (MkRewriting st)
         ,MkDPProblem (MkRewriting st) (NarradarTRS t Var)
         ,ICap t Var (MkRewriting st, NarradarTRS t Var)
         ,IUsableRules t Var (MkRewriting st) (NarradarTRS t Var)
         ) =>
    Processor info FInstantiation (NarradarProblem (MkRewriting st) t) (NarradarProblem (MkRewriting st) t) where
  applySearch FInstantiation = finstantiation

instance (Info info (NarradarProblem b t)
         ,Processor info FInstantiation (NarradarProblem b t) (NarradarProblem b t)
         ) =>
    Processor info FInstantiation (NarradarProblem (MkNarrowing b) t) (NarradarProblem (MkNarrowing b) t) where
  applySearch = liftProcessorS

instance (v ~ Var
         ,t ~ f (DPIdentifier id), MapId f
         ,TermId t ~ DPIdentifier id, HasId t, Unify t
         ,Pretty typ
         ,MkDPProblem typ (NarradarTRS t Var)
         ,Traversable (Problem typ)
         ,Pretty (t(Term t v)), Ord(t(Term t v))
         ,IUsableRules t v typ (NarradarTRS t v)
         ,ICap t v (typ, (NarradarTRS t Var))
         ,Info info GraphTransformationProof
         ) =>
    Processor info FInstantiation (NarradarProblem (InitialGoal t typ) t)
                                  (NarradarProblem (InitialGoal t typ) t)
 where
 applySearch FInstantiation p@InitialGoalProblem{..}
  | null currentPairs      = [return p]
  | not $ isDPTRS (getP p) = error "finstantiationProcessor: expected a problem carrying a DPTRS"
  | isCollapsing (getR p)  = mzero  -- no point in instantiating everything around
  | otherwise = [ singleP (FInstantiationProof olddp newdps) p (mkDerivedDPProblem typ' p')
                     | (i, olddp, newdps) <- dpss
                     , let dgraph'= expandDGraph p olddp newdps
                     , let typ'   = InitialGoal goals (Just dgraph') (getProblemType baseProblem)
                     , let p'     = expandDPair (getBaseProblem p) i newdps
                ]
   where currentPairs =  [0..] `zip` tag (fromMaybe err . (`lookupNode` dgraph)) (rules$ getP p)
         dpss = [ (i, olddp, newdps)
                              | (i,(j,olddp)) <-currentPairs
                              , let newdps = f j olddp
                              , not (null newdps)]
         err = error "Instantiation processor: unexpected"

         f i olddp@(s :-> t)
                  | EqModulo olddp `notElem` (EqModulo <$> newdps) = newdps
                  | otherwise = []
              where
                gr       = fullgraph dgraph
                allPairs = pairs dgraph
                newdps    = [applySubst sigma s :-> applySubst sigma t
                             | Just sigma <- snub [dpUnifyInv allPairs j i
                                                       | j <- safeAt "FInstantiation" gr i]]


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

-- ----------------
-- Implementation
-- ----------------
-- Narrowing

narrowing, narrowing_innermost
          :: (p  ~ Problem typ trs
             ,trs ~ NarradarTRS t v
             ,v ~ Var
             ,TermId t  ~ DPIdentifier id, HasId t, Unify t
             ,Enum v, GetVars v v, Ord (Term t v)
             ,MkDPProblem typ trs, Traversable (Problem typ)
             ,IUsableRules t v typ trs, ICap t v (typ,trs)
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
              |  isLinear t
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
             ,TermId t  ~ DPIdentifier id, HasId t, Unify t
             ,Enum v, GetVars v v, Ord (t(Term t v))
             ,MkDPProblem typ trs, Traversable (Problem typ)
             ,IUsableRules t v typ (NarradarTRS t v)
             ,ICap t v (typ,trs)
             ,Pretty (t(Term t v)), Pretty v, Pretty typ
             ,Info info (Problem (InitialGoal t typ) trs)
             ,Info info GraphTransformationProof
             ,Monad mp
             ) =>
             Problem (InitialGoal t typ) trs -> [Proof info mp (Problem (InitialGoal t typ) trs)]
narrowingIG p0@InitialGoalProblem{..}
  | null currentPairs       = [return p0]
  | not $ isDPTRS (getP p0) = error "narrowingIG Processor: expected a problem carrying a DPTRS"
  | otherwise  = [ singleP (NarrowingProof olddp newdps) p0
                           (mkDerivedDPProblem typ' (expandDPair (getBaseProblem p0) i newdps))
                     | (i, olddp, newdps) <- dpss
                     , let dgraph' = expandDGraph p0 olddp newdps
                     , let typ'    = InitialGoal goals (Just dgraph') (getProblemType baseProblem)]
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

narrowing_innermostIG p0@InitialGoalProblem{..}
  | null currentPairs       = [return p0]
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (NarrowingProof olddp newdps) p0
                          (mkDerivedDPProblem typ' (expandDPair (getBaseProblem p0) i newdps))
                     | (i, olddp, newdps) <- dpss
                     , let dgraph'= expandDGraph p0 olddp newdps
                     , let typ'   = InitialGoal goals (Just dgraph') (getProblemType baseProblem)]
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
             ,TermId t ~ DPIdentifier id, HasId t, Unify t
             ,Enum v, GetVars v v
             ,MkDPProblem typ trs, Traversable (Problem typ)
             ,Pretty ((Term t v)), Ord(Term t v), Pretty v, Pretty typ
             ,IUsableRules t v typ (NarradarTRS t v), ICap t v (typ, trs)
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
