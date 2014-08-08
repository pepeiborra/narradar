{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
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
import Control.Arrow (second)
import Control.DeepSeq
import Control.Monad.Identity (Identity(..))
import Control.Monad.Logic
import Data.Array.IArray hiding ((!), array)
import qualified Data.Array.IArray as A
import qualified Data.Foldable as F
import Data.Functor.Two
import qualified Data.Graph as Gr
import Data.List (foldl1', isPrefixOf, groupBy, nub, sort)
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Data.Typeable
import Text.XHtml (HTML)

import Narradar.Types hiding (narrowing, rewriting)
import Narradar.Types.TRS
import Narradar.Constraints.Confluence
import Narradar.Framework
import Narradar.Framework.GraphViz
import Narradar.Framework.Ppr
import Narradar.Utils hiding (O)

import Data.Term.Rewriting
import Data.Term.Narrowing
import qualified Data.Term as Term
import Data.Term.Rules()

import qualified Data.Term.Family as Family

import Debug.Hoed.Observe

data NarrowingP     (info :: * -> *) = NarrowingP    {restrict :: Maybe [Position]} deriving (Generic, Typeable)
data Instantiation  (info :: * -> *) = Instantiation deriving (Generic, Typeable)
data FInstantiation (info :: * -> *) = FInstantiation deriving (Generic, Typeable)
data RewritingP     (info :: * -> *) = RewritingP deriving (Generic, Typeable)

type instance InfoConstraint (NarrowingP info) = info
type instance InfoConstraint (RewritingP info) = info
type instance InfoConstraint (Instantiation info) = info
type instance InfoConstraint (FInstantiation info) = info

instance Observable1 info => Observable (NarrowingP     info)
instance Observable1 info => Observable (Instantiation  info)
instance Observable1 info => Observable (FInstantiation info)
instance Observable1 info => Observable (RewritingP     info)

-- * Narrowing
-- ------------

instance ( t ~ f (DPIdentifier id)
         , Family.Id t ~ DPIdentifier id
         , Info info GraphTransformationProof
         , FrameworkN Rewriting t Var
         ) =>
  Processor (NarrowingP info) (NarradarProblem Rewriting t) where
  type Typ (NarrowingP info) (NarradarProblem Rewriting t) = Rewriting
  type Trs (NarrowingP info) (NarradarProblem Rewriting t) = NarradarTRS t Var
  applySearchO o NarrowingP{} = narrowing o

instance ( t ~ f (DPIdentifier id)
         , Family.Id t ~ DPIdentifier id
         , FrameworkN IRewriting t Var
         , Info info GraphTransformationProof

         ) =>
  Processor (NarrowingP info) (NarradarProblem IRewriting t) where
  type Typ (NarrowingP info) (NarradarProblem IRewriting t) = IRewriting
  type Trs (NarrowingP info) (NarradarProblem IRewriting t) = NarradarTRS t Var
  applySearchO o NarrowingP{} = narrowing_innermost o

instance ( t ~ f (DPIdentifier id)
         , Family.Id t ~ DPIdentifier id
         , Info info GraphTransformationProof
         , FrameworkN (QRewriting (Term t Var)) t Var
         ) =>
  Processor (NarrowingP info) (NarradarProblem (QRewriting (Term t Var)) t) where
  type Typ (NarrowingP info) (NarradarProblem (QRewriting (Term t Var)) t) = QRewriting (Term t Var)
  type Trs (NarrowingP info) (NarradarProblem (QRewriting (Term t Var)) t) = NarradarTRS t Var
  applySearchO (O o oo) NarrowingP{restrict} p0@(QRewritingProblem _ _ q _ qCondition)
   | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
   | otherwise  = [ singleP (NarrowingProof p olddp newdps) p0 (oo "expand" expandDPairO p0 i newdps)
                     | (i, narrowings) <- dpss
                     , (p, newdps) <- narrowings
                     , let olddp  = safeAt "narrowing" dpsA i
                     ]
    where
          (dpsA, o "gr" -> gr) = (rulesArray (getP p0), rulesGraph (getP p0))
          dpsA' = runIcap p0 $ getFresh dpsA
          dpss = zip [0..] (map (oo "f" f) $ assocs dpsA')

          f (O o oo) (i, olddp@(s :-> t))
              | (null (qset q) && isLinear t) || qCondition
              , not (null newdps)
              = newdps

              | otherwise = []
               where
                 narrowingsByPos = map (\g -> (snd (head g), map fst g))
                                 $ groupBy ((==) `on` snd)
                                 $ oo "qNarrow1DP" qNarrow1DPO q (rules $ getR p0) olddp
                 newdps =
                          [ (p, dps)
                          -- For every valid position p, collect all the narrowings below it
                          | (p, dps) <- [ (p, [ n
                                              | (p', subnarrowings) <- o "narrowingsByPos" narrowingsByPos
                                              ,  p `isPrefixOf` p'
                                              , n <- subnarrowings ])
                                   | p <- map fst narrowingsByPos
                                   , any (`isPrefixOf` p) validPos
                                   ]
                          , EqModulo olddp `notElem` (EqModulo <$> dps)
                          -- extra condition to avoid specializing to pairs whose rhs are variables
                          -- (I don't recall having seen this in any paper but surely is common knowledge)
                          , none(isVar.rhs) dps ]

                 uu     = o "uu" $ map (lhs . (safeAt "narrowing" dpsA)) (o "gr_i" $ safeAt "narrowing" gr i)
--                 pos_uu = mconcat (Set.fromList . positions <$> uu)
                 pos_t  = oo "pos_t" $ \(O o oo) ->
                          Set.fromList $ positions $ o "icap" $ runIcap (getVars p0) $
                            (getFresh t >>= icap p0 [s])
                 pos_uu = intersections $ o "pos_uu" $ map Set.fromList $ flip map uu $ o "pos_uu\\" $ \u -> do
                    p <- positions u
                    guard (Set.member p pos_t)
                    case unify (u!p) (t!p) of
                      Just mu -> guard$ not(inQNF (applySubst mu s) q || inQNF (applySubst mu u) q)
                      Nothing -> return ()
                    return p
                 pos_qnf  = Set.fromList $ filter (\p -> not(inQNF (t ! p) q)) (positions t)
                 validPos = oo "validPos" $ \(O o oo) ->
                            o "restrict & valid"
                          $ Set.toList
                          $ maybe id (Set.intersection . o "restrict" . Set.fromList) restrict
                          $ o "valid" (Set.union (o "uu" pos_uu) (o "qnf" pos_qnf))


-- Liftings

instance (Processor (NarrowingP info) (Problem b trs)
         ,Info info (Problem b trs)
         ,Observable b, Observable trs
         ,Problem b trs ~ Res (NarrowingP info) (Problem b trs)
         ,FrameworkProblem b trs
         ) =>
  Processor (NarrowingP info) (Problem (MkNarrowing b) trs) where
  type Typ (NarrowingP info) (Problem (MkNarrowing b) trs) = MkNarrowing b
  type Trs (NarrowingP info) (Problem (MkNarrowing b) trs) = trs
  applySearchO = liftProcessorS

instance (Processor (NarrowingP info) (Problem b trs)
         ,Info info (Problem b trs)
         ,Observable b, Observable trs
         ,Problem b trs ~ Res (NarrowingP info) (Problem b trs)
         ,FrameworkProblem b trs
         ) =>
  Processor (NarrowingP info) (Problem (MkNarrowingGen b) trs) where
  type Typ (NarrowingP info) (Problem (MkNarrowingGen b) trs) = MkNarrowingGen b
  type Trs (NarrowingP info) (Problem (MkNarrowingGen b) trs) = trs
  applySearchO = liftProcessorS

-- Not so straightforward liftings

instance ( Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , Info info GraphTransformationProof
         , FrameworkN (InitialGoal t Rewriting) t Var
         , FrameworkId id
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t Rewriting) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t Rewriting) t) = InitialGoal t Rewriting
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t Rewriting) t) = NarradarTRS t Var
   applySearchO o tag = narrowingIG o

instance ( Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , Observable id
         , Info info GraphTransformationProof
         , FrameworkN (InitialGoal t IRewriting) t Var
         , FrameworkId id
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t IRewriting) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t IRewriting) t) = InitialGoal t IRewriting
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t IRewriting) t) = NarradarTRS t Var
   applySearchO o tag = narrowing_innermostIG o

instance ( Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , FrameworkN (InitialGoal t Narrowing) t Var
         , FrameworkId id
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t Narrowing) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t Narrowing) t) = InitialGoal t Narrowing
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t Narrowing) t) = NarradarTRS t Var
   applySearchO o tag = narrowingIG o

instance ( Family.Id t ~ DPIdentifier id
         , t ~ f (DPIdentifier id), MapId f
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , Info info GraphTransformationProof
         , FrameworkN (InitialGoal t CNarrowing) t Var
         , FrameworkId id
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowing) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowing) t) = InitialGoal t CNarrowing
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowing) t) = NarradarTRS t Var
   applySearchO o tag = narrowing_innermostIG o

instance ( Family.Id t ~ DPIdentifier (GenId id)
         , t ~ f (DPIdentifier (GenId id)), MapId f
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , FrameworkN (InitialGoal t NarrowingGen) t Var
         , FrameworkId (GenId id)
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t NarrowingGen) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t NarrowingGen) t) = InitialGoal t NarrowingGen
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t NarrowingGen) t) = NarradarTRS t Var
   applySearchO o tag = narrowingIG o

instance ( Family.Id t ~ DPIdentifier (GenId id)
         , t ~ f (DPIdentifier (GenId id)), MapId f
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , FrameworkN (InitialGoal t CNarrowingGen) t Var
         , FrameworkId (GenId id)
         , Info info GraphTransformationProof
         )=> Processor (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowingGen) t)
  where
   type Typ (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowingGen) t) = InitialGoal t CNarrowingGen
   type Trs (NarrowingP info) (NarradarProblem (InitialGoal t CNarrowingGen) t) = NarradarTRS t Var
   applySearchO o tag = narrowing_innermostIG o

-- * Instantiation
-- ---------------

instance (trs ~ NarradarTRS t Var
         ,t ~ f(DPIdentifier id), MapId f
         ,DPIdentifier id ~ Family.Id t
         ,Info info GraphTransformationProof, Pretty (MkRewriting st)
         ,FrameworkId id
         ,FrameworkN (MkRewriting st) t Var
         ) =>
    Processor (Instantiation info) (NarradarProblem (MkRewriting st) t) where
  type Typ (Instantiation info) (NarradarProblem (MkRewriting st) t) = MkRewriting st
  type Trs (Instantiation info) (NarradarProblem (MkRewriting st) t) = NarradarTRS t Var
  applySearchO o Instantiation = instantiation o

instance (Info info (NarradarProblem b t)
         ,Processor (Instantiation info) (NarradarProblem b t)
         ,Observable b, Observable (Term t Var)
         ,NarradarProblem b t ~ Res (Instantiation info) (NarradarProblem b t)
         ,FrameworkN b t Var
         ) =>
    Processor (Instantiation info) (NarradarProblem (MkNarrowing b) t) where
  type Typ (Instantiation info) (NarradarProblem (MkNarrowing b) t) = MkNarrowing b
  type Trs (Instantiation info) (NarradarProblem (MkNarrowing b) t) = NarradarTRS t Var
  applySearchO = liftProcessorS

instance (trs ~ NarradarTRS t Var
         ,t ~ f(DPIdentifier id), MapId f
         ,DPIdentifier id ~ Family.Id t
         ,Info info GraphTransformationProof
         ,FrameworkId id, NFData (Term t Var)
         ,FrameworkN (QRewriting (Term t Var)) t Var
         ) =>
    Processor (Instantiation info) (NarradarProblem (QRewriting (Term t Var)) t) where
  type Typ (Instantiation info) (NarradarProblem (QRewriting (Term t Var)) t) = QRewriting (Term t Var)
  type Trs (Instantiation info) (NarradarProblem (QRewriting (Term t Var)) t) = NarradarTRS t Var
--  applySearchO o Instantiation = instantiation o
  applySearchO (O o oo) Instantiation p
   | null dps  = error "instantiationProcessor: received a problem with 0 pairs"
   | not $ isDPTRS (getP p) = error "instantiationProcessor: expected a problem carrying a DPTRS"
   | otherwise = [ singleP (InstantiationProof olddp newdps) p (expandDPair p i newdps)
                     | (i, newdps) <- dpss
                     , let olddp  = safeAt "instantiation" dpsA i
                     ]

   where (dpsA, gr) = (rulesArray (getP p), o "gr" $ rulesGraph (getP p))
         edges = o "edges" (Gr.edges gr)
         dps  = elems dpsA
         dpss = [ (i, dps) | Just (i,dps) <- map (oo "f" f) (assocs dpsA)
                           , not (null dps)]

         f (O o oo) (i,olddp@(s :-> t))
                  | o "isNotIncluded" isNotIncluded olddp newdps = Just (i, newdps)
                  | otherwise = Nothing
            where newdps = [ deepseq sigma_r $
                              applySubst sigma_l s :-> applySubst sigma_l t
                            | Just (Two sigma_r sigma_l) <-
                                 snub [o "dpUnify" (dpUnify (getP p)) l r
                                       | (r,l) <- edges, l == i]]

isNotIncluded olddp newdps = EqModulo olddp `notElem` (EqModulo <$> newdps)


instance (trs ~ NarradarTRS t v
         ,v   ~ Var
         ,t   ~ f id, MapId f
         ,id  ~ Family.Id t
         ,Observable (Term t Mode)
         ,Info info GraphTransformationProof
         ,FrameworkN (InitialGoal t typ) t Var
         ,FrameworkId id, DPSymbol id
         ) =>
    Processor (Instantiation info) (NarradarProblem (InitialGoal (f id) typ) (f id))
 where
  type Typ (Instantiation info) (NarradarProblem (InitialGoal (f id) typ) (f id)) = InitialGoal (f id) typ
  type Trs (Instantiation info) (NarradarProblem (InitialGoal (f id) typ) (f id)) = NarradarTRS (f id) Var
  applySearchO (O o oo) Instantiation p@InitialGoalProblem{dgraph}
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
              newdps   = [ applySubst sigma_r s :-> applySubst sigma_r t
                          | Just (Two sigma_r sigma_l) <- snub [dpUnify allPairs i m | (m,n) <- Gr.edges gr, n == i]
                         ]


-- * Forward Instantiation
-- -----------------------

instance (trs ~ NarradarTRS t Var
         ,t ~ f (DPIdentifier id), MapId f
         ,DPIdentifier id ~ Family.Id t
         ,Info info GraphTransformationProof
         ,FrameworkN (MkRewriting st) t Var
         ,FrameworkId id
         ) =>
    Processor (FInstantiation info) (NarradarProblem (MkRewriting st) t) where
  type Typ (FInstantiation info) (NarradarProblem (MkRewriting st) t) = MkRewriting st
  type Trs (FInstantiation info) (NarradarProblem (MkRewriting st) t) = NarradarTRS t Var
  applySearchO o FInstantiation = finstantiation o

instance (Info info (NarradarProblem b t)
         ,Processor (FInstantiation info) (NarradarProblem b t)
         ,NarradarProblem b t ~ Res (FInstantiation info) (NarradarProblem b t)
         ,FrameworkN b t Var
         ) =>
 Processor (FInstantiation info) (NarradarProblem (MkNarrowing b) t) where
 type Typ (FInstantiation info) (NarradarProblem (MkNarrowing b) t) = MkNarrowing b
 type Trs (FInstantiation info) (NarradarProblem (MkNarrowing b) t) = NarradarTRS t Var
 applySearchO = liftProcessorS

instance (trs ~ NarradarTRS t Var
         ,t ~ f(DPIdentifier id), MapId f
         ,DPIdentifier id ~ Family.Id t
         ,Info info GraphTransformationProof
         ,FrameworkId id, NFData (Term t Var)
         ,FrameworkN (QRewriting (Term t Var)) t Var
         ) =>
    Processor (FInstantiation info) (NarradarProblem (QRewriting (Term t Var)) t) where
  type Typ (FInstantiation info) (NarradarProblem (QRewriting (Term t Var)) t) = QRewriting (Term t Var)
  type Trs (FInstantiation info) (NarradarProblem (QRewriting (Term t Var)) t) = NarradarTRS t Var
  applySearchO o FInstantiation = finstantiation o

instance (v ~ Var
         ,t ~ f (DPIdentifier id), MapId f
         ,Family.Id t ~ DPIdentifier id
         ,Pretty typ
         ,Info info GraphTransformationProof
         ,Observable (Term t Mode)
         ,FrameworkN (InitialGoal t typ) t Var
         ,FrameworkId id
         ) =>
    Processor (FInstantiation info) (NarradarProblem (InitialGoal t typ) t)
 where
 type Typ (FInstantiation info) (NarradarProblem (InitialGoal t typ) t) = InitialGoal t typ
 type Trs (FInstantiation info) (NarradarProblem (InitialGoal t typ) t) = NarradarTRS t Var
 applySearchO o FInstantiation p@InitialGoalProblem{dgraph}
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
                newdps    = [applySubst sigma_l s :-> applySubst sigma_l t
                             | Just (Two sigma_r sigma_l) <- snub [ dpUnifyInv allPairs j i
                                                                  | j <- safeAt "FInstantiation" gr i]]

-- * Rewriting
-- ------------

instance ( t ~ f id, v ~ Var
         , Info info GraphTransformationProof
         , FrameworkN IRewriting t Var
         ) =>
    Processor (RewritingP info) (NarradarProblem IRewriting t)
 where
  type Typ (RewritingP info) (NarradarProblem IRewriting t) = IRewriting
  type Trs (RewritingP info) (NarradarProblem IRewriting t) = NarradarTRS t Var
  applySearchO o RewritingP p0 = problems
    where
     redexes t = [ p | p <- positions t, not (isNF (rules $ getR p0) (t!p))]

     problems = [ singleP (RewritingProof olddp (s:->t')) p0 (expandDPair p0 i [s:->t'])
                | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
                , p <- redexes t
                , let urp = getR$  iUsableRules' p0 [] [t!p]
                , isNonOverlapping urp
                , [t'] <- [rewrite1p (rules urp) t p]
                ]

instance ( t ~ f id, MapId f
         , Info info GraphTransformationProof
         , Eq (GoalTerm t)
         , Observable (Term t Mode)
         , FrameworkN (InitialGoal t IRewriting) t Var
         , FrameworkId id, DPSymbol id
         ) =>
    Processor (RewritingP info) (NarradarProblem (InitialGoal t IRewriting) t)
 where
  type Typ (RewritingP info) (NarradarProblem (InitialGoal t IRewriting) t) = InitialGoal t IRewriting
  type Trs (RewritingP info) (NarradarProblem (InitialGoal t IRewriting) t) = NarradarTRS t Var
  applySearchO o RewritingP p0 =
         [ singleP (RewritingProof olddp newdp) p0 p'
               | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
               , p <- redexes t
               , let urp = getR $ iUsableRules' p0 [] [t!p]
               , isNonOverlapping urp
               , [t'] <- [rewrite1p (rules urp) t p]
               , let newdp = s:->t'
                     p' = expandDGraph (expandDPair p0 i [newdp]) olddp [newdp]
               ]
    where
      redexes t = [ p | p <- positions t, not(isNF (rules $ getR p0) (t!p))]


instance ( t ~ f id, v ~ Var
         , Info info GraphTransformationProof
         , FrameworkN (QRewriting (Term t Var)) t Var
         , Observable (SomeInfo info)
         ) =>
    Processor (RewritingP info) (NarradarProblem (QRewriting (Term t Var)) t)
 where
  type Typ (RewritingP info) (NarradarProblem (QRewriting (Term t Var)) t) = QRewriting (Term t Var)
  type Trs (RewritingP info) (NarradarProblem (QRewriting (Term t Var)) t) = NarradarTRS t Var
  applySearchO (O o oo) RewritingP p0 = problems
    where
     redexes t = [ p | p <- positions t, not (isNF (rules $ getR p0) (t!p))]

     problems = [ problem
                | ir <- zip [0..] (rules $ getP p0)
                , problem <- oo "tryRule" tryRule ir
                ]

     tryRule (O o oo) (i, olddp@(s:->t)) =
                [ singleP (RewritingProof olddp (s:->t')) p0 (expandDPair p0 i [s:->t'])
                | p <- o "redexes" $ redexes t
                , let urp = o "urp" $ getR $ iUsableRules' p0 [s] [t!p]
                , o "isQConfluent" $ isQConfluent (q p0) (rules urp)
                , lr <- map (`getVariant` urp) $ rules urp
                , t' <- o "rewrite1" rewrite1p [lr] t p
                , o "all critical pairs are trivial" $
                  all (\(p,l,r) -> l == r) (criticalPairsOf lr (rules urp))
                ]

-- -------
-- Proofs
-- -------

data GraphTransformationProof where
    NarrowingProof :: (PprTPDB (Rule t v), Pretty (Rule t v), Ord (Term t v)) =>
                      Position
                   ->  Rule t v           -- ^ Old pair
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

    deriving (Typeable)

instance Eq GraphTransformationProof  where a == b = pPrint a == pPrint b
instance Ord GraphTransformationProof where compare a b = compare (pPrint a) (pPrint b)
instance Observable GraphTransformationProof where
  observer = observeOpaque "GraphTransformationProof"

instance Pretty GraphTransformationProof where
  pPrint (NarrowingProof pos old new) =
                                 text "Narrowing Processor" <+> parens(text "below position" <+> pos) $+$
                                 text "Pair" <+> pPrint old <+>
                                 text "replaced by" $$ (vcat $ map pPrint $ sort new)

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
             ,Family.Id t  ~ DPIdentifier id, HasId1 t, Unify t
             ,Info info p
             ,Info info GraphTransformationProof
             ,Monad mp
             ,FrameworkProblem typ trs
             ) =>
             Observer -> Problem typ trs -> [Proof info mp (Problem typ trs)]

narrowing o p0
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise  = [ singleP (NarrowingProof [] olddp newdps) p0 (expandDPair p0 i newdps)
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
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0 [])))
                                        `Set.intersection` pos_uu)
                              , any (`isPrefixOf` p) validPos]
              =  -- extra condition to avoid specializing to pairs whose rhs are variables
                 -- (I don't recall having seen this in any paper but surely is common knowledge)
                 if any (isVar.rhs.snd) new_dps then [] else new_dps

              | otherwise = []
               where uu     = map (lhs . (safeAt "narrowing" dpsA)) (safeAt "narrowing" gr i)
                     pos_uu = if null uu then Set.empty
                                else foldl1' Set.intersection (Set.fromList . positions <$> uu)

narrowing_innermost o p0
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (NarrowingProof [] olddp newdps) p0 (expandDPair p0 i newdps)
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
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0 [])))
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
             ,Family.Id t  ~ DPIdentifier id
             ,FrameworkN (InitialGoal t typ) t v
             ,FrameworkId id, Pretty (DPIdentifier id)
             ,Info info (Problem (InitialGoal t typ) trs)
             ,Info info GraphTransformationProof
             ,Monad mp
             ,Observable (Term t Mode)
             ,Observable (DPIdentifier id)
             ) =>
             Observer -> Problem (InitialGoal t typ) trs -> [Proof info mp (Problem (InitialGoal t typ) trs)]
narrowingIG o p0@InitialGoalProblem{dgraph}
  | not $ isDPTRS (getP p0) = error "narrowingIG Processor: expected a problem carrying a DPTRS"
  | otherwise  = [ singleP (NarrowingProof [] olddp newdps) p0 p'
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
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0 [])))
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

narrowing_innermostIG o p0@InitialGoalProblem{dgraph}
  | not $ isDPTRS (getP p0) = error "narrowingProcessor: expected a problem carrying a DPTRS"
  | otherwise = [ singleP (NarrowingProof [] olddp newdps) p0 p'
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
                                     = Set.toList(Set.fromList(positions (runIcap (getVars p0) (getFresh t >>= icap p0 [])))
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

narrow1DP rr (l :-> r) = [ (Term.applySubst theta l :-> r', p)
                           | ((r',p),theta) <- observeAll (narrow1P rr r) ]

--qNarrow1DPO :: Observer -> QSet (TermN id) -> [RuleN id] -> RuleN id -> [(RuleN id, Position)]
qNarrow1DPO (O o oo) qset@(QSet q) rr (l :-> r) =
  [ (l' :-> r', p)
  | ((r',p),theta) <- observeAll (qNarrow1P' q rr r)
  , let l' = applySubst (o "theta" $ liftSubstNF theta) l
  , inQNF l' qset]

-- Instantiation

instantiation, finstantiation
          :: forall typ trs mp t f v p id info.
             (p  ~ Problem typ trs, Info info p
             ,trs ~ NarradarTRS t v
             ,v ~ Var
             ,t ~ f (DPIdentifier id)
             ,Family.Id t ~ DPIdentifier id
             ,Info info GraphTransformationProof
             , FrameworkProblem typ trs
             , FrameworkId id
             ,Monad mp
             ) =>
             Observer -> Problem typ trs -> [Proof info mp (Problem typ trs)]

instantiation o p
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
            where newdps = [ (i, applySubst sigma_l s :-> applySubst sigma_l t)
                            | Just (Two sigma_r sigma_l) <-
                                snub [dpUnify (getP p) i m | (m,n) <- Gr.edges gr, n == i]]

--instantiation p = [return p]

-- Forward instantiation

finstantiation (O o oo) p
  | null dps  = error "forward instantiation Processor: received a problem with 0 pairs"
  | not $ isDPTRS (getP p) = error "finstantiationProcessor: expected a problem carrying a DPTRS"
--  | o "isCollapsing" (isCollapsing (getR p)) = mzero
  | otherwise = [ singleP (FInstantiationProof olddp newdps) p
                           (expandDPair p i newdps)
                     | (i, dps') <- dpss
                     , let olddp  = safeAt "finstantiation" dpsA  i
                     , let newdps = dps' !! i]
   where (dpsA, gr) = (rulesArray (getP p), rulesGraph (getP p))
         dps  = elems dpsA
         dpss = [ (i, snd <$$> dps) | (i,dps) <- zip [0..] (maps (oo "f" f) (assocs dpsA))
                                    , all (not.null) dps]
         f (O o oo) (i, olddp@(s :-> t))
                  | EqModulo olddp `notElem` (EqModulo . snd <$> newdps) = newdps
                  | otherwise = []
              where newdps = [(i, applySubst sigma_r s :-> applySubst sigma_r t)
                             | Just (Two sigma_r sigma_l) <-
                                 snub [ dpUnifyInv (getP p) j i
                                      | j <- safeAt "finstantiation" gr i]]
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

rewriting o p0
    | [p] <- problems = p
    | otherwise = dontKnow RewritingFail p0
    where
     redexes t = [ p | p <- positions t, isJust (rewrite1 (rules $ getR p0) t)]

     problems = [ singleP (RewritingProof olddp (s:->t')) p0 (expandDPair p0 i [s:->t'])
                | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
                , [p] <- [redexes t]
                , let urp = iUsableRules' p0 [] [t!p]
                , isNonOverlapping urp
                , [t'] <- [rewrite1p (rules urp) t p]
                ]

rewritingGoal o p0
    | [x] <- problem = x
    | otherwise = dontKnow RewritingFail p0
   where
    problem = [ singleP (RewritingProof olddp newdp) p0 p'
                | (i, olddp@(s :-> t)) <- zip [0..] (rules $ getP p0)
                , [p] <- [redexes t]
                , let urp = iUsableRules' p0 [] [t!p]
                , isNonOverlapping urp
                , [t'] <- [rewrite1 (rules urp) t]
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
