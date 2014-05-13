{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns, DisambiguateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

module Narradar.Constraints.SAT.RPOAF (
   SATSymbol(..), UsableSymbolRes(..), prec, filtering, status, theSymbolR
  ,RPOSsymbol(..), RPOsymbol(..), LPOsymbol(..), LPOSsymbol(..), MPOsymbol(..)
  ,rpoAF_DP, rpoAF_NDP, rpoAF_IGDP
  ,rpo, rpos, lpo, lpos, mpo
  ,verifyRPOAF, isCorrect
  ,omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone
  ,Usable, UsableSymbol(..)
  ) where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Control.Monad.Cont
import Control.Monad.List
import Control.Monad.Reader
import Data.Bifunctor
import Data.Foldable (Foldable, toList)
import Data.List ((\\), find, transpose, inits, tails)
import Data.Maybe
import Data.Monoid
import Data.Hashable
import Data.Traversable (traverse)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import qualified Funsat.RPOCircuit.Symbols as Funsat
import Funsat.RPOCircuit (Co, CoRPO, assertCircuits)
import Funsat.RPOCircuit.Symbols (Natural(..), LPOSsymbol(..), LPOsymbol(..), MPOsymbol(..), RPOSsymbol(..), RPOsymbol(..), mkSymbolDecoder)

import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.Syntactic
import Narradar.Constraints.SAT.MonadSAT
import Narradar.Constraints.SAT.RPOAF.Symbols
import Narradar.Framework
import Narradar.Types (DPSymbol)
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Problem
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGen
import qualified Narradar.Types as Narradar
import Narradar.Utils

import qualified Data.Term.Family as Family
import qualified Narradar.Types.ArgumentFiltering as AF
import qualified Prelude as P
import Prelude hiding (lex, not, and, or, any, all, quot, (>))

class SATSymbol sid where
  mkSATSymbol :: (v  ~ Family.Var sid
                 ,id ~ Family.Id sid
                 ,Decode v Bool, Show id, Co repr v, MonadSAT repr v m) =>
                 (id, Int) -> m (sid, repr v)

instance SATSymbol (Usable(RPOSsymbol v id)) where mkSATSymbol = rpos
instance SATSymbol (Usable(RPOsymbol  v id)) where mkSATSymbol = rpo
instance SATSymbol (Usable(LPOSsymbol v id)) where mkSATSymbol = lpos
instance SATSymbol (Usable(LPOsymbol  v id)) where mkSATSymbol = lpo
instance SATSymbol (Usable(MPOsymbol  v id)) where mkSATSymbol = mpo

-- | RPO + AF

rpoAF :: (id ~ Family.Id trs
         ,id ~ Family.Id sid
         ,v  ~ Family.Var sid
         ,Rule (TermF id) tv ~ Family.Rule trs
         ,TermF sid ~ Family.TermF repr
         ,Eq tv
         ,Ord sid, Show id, Pretty id
         ,HasSignature trs
         ,HasRules trs
         ,SATSymbol sid
         ,Pretty sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,RPOExtCircuit repr sid, CoRPO repr (TermF sid) tv v
         ,Decode v Bool
         ,MonadReader r mr
         ,MonadSAT repr v m
         ,v ~ Var) =>
         Bool -> trs -> m( mr ((), r, [sid]))
rpoAF allowCol trs = runRPOAF allowCol (getSignature trs) $ \dict -> do
  let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  let problem = and [ l > r | l:->r <- symb_rules]
  assert [problem]
  return (return ())


-- | Returns the indexes of non decreasing pairs and the symbols used
rpoAF_DP ::
         (trs  ~ NarradarTRS (TermF id) tv
         ,trs' ~ NarradarTRS (TermF sid) tv
         ,id   ~ Family.Id trs
         ,id   ~ Family.Id sid
--         ,v    ~ Family.Var repr
         ,v    ~ Family.Var sid
--         ,v    ~ Family.Var v
         ,TermF sid ~ Family.TermF repr
         ,Ord id, Show id
         ,Ord tv
         ,MkDPProblem typ trs'
         ,SATSymbol sid
         ,Ord sid, Pretty sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,RPOExtCircuit repr sid, CoRPO repr (TermF sid) tv v
         ,UsableSymbol sid
         ,Decode v Bool
         ,MonadSAT repr v m
         ,v ~ Var) =>
         Bool -> (Problem typ trs' -> repr v) -> Problem typ trs
         -> m (EvalM v ([Int], BIEnv v, [sid]))

rpoAF_DP allowCol omega p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs'    = mapNarradarTRS convert (getR p)
      dps'    = mapNarradarTRS convert (getP p)
      p'      = mkDPProblem (getFramework p) trs' dps'

  decreasing_dps <- replicateM (length $ rules dps') boolean

  () <- pprTrace (text "Asserting omega") $ return ()
  assertAll [omega p']

  () <- pprTrace (text "asserting decreasingness of rules") $ return ()
  assertAll [ l >~ r | l:->r <- rules dps']

  () <- pprTrace (text "asserting decreasingness of pairs") $ return ()
  assertAll [(l > r) <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  () <- pprTrace (text "asserting that at least one pair is decreassing") $ return ()
  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  () <- pprTrace (text "assert that we find the best solution possible") $ return ()
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  () <- pprTrace (text "assert that only usable rules are selected") $ return ()
  mapM_ (assertW 1 . (:[]) . not . input . usable) (Map.elems dict)

  return $ do
    decreasing <- decode decreasing_dps
    let the_non_decreasing_pairs = [ r | (r,False) <- zip [(0::Int)..] decreasing]
    return the_non_decreasing_pairs

rpoAF_IGDP :: forall initialgoal initialgoal' problem problem' trs trs' id sid satSymbol repr m tv v base extraConstraints.
         (initialgoal  ~ InitialGoal (TermF id) base
         ,initialgoal' ~ InitialGoal (TermF sid) base
         ,problem  ~ Problem initialgoal trs
         ,problem' ~ Problem initialgoal' trs'
         ,trs      ~ NarradarTRS (TermF id) tv
         ,trs'     ~ NarradarTRS (TermF sid) tv
         ,id       ~ Family.Id sid
         ,v        ~ Family.Var sid
         ,v        ~ Family.Var v
         ,TermF sid~ Family.TermF repr
         ,Ord sid
         ,Ord id, Show id
         ,Ord tv
         ,Traversable (Problem base), Pretty base
         ,MkDPProblem initialgoal' (NTRS sid)
         ,IsDPProblem base
         ,SATSymbol sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,RPOExtCircuit repr sid, CoRPO repr (TermF sid) tv v
         ,UsableSymbol sid
         ,MkDPProblem initialgoal' trs'
--         ,Decode sid (SymbolRes id) v
         ,MonadSAT repr v m
         ,v ~ Var
         ) =>
            Bool
         -> (problem' -> (repr v, EvalM v extraConstraints))
         -> problem
         -> m (EvalM v ( ([Int], extraConstraints), BIEnv v, [sid]))

rpoAF_IGDP allowCol omega p@InitialGoalProblem{..}
  = runRPOAF allowCol (getSignature p `mappend` getSignature (pairs dgraph)) $ \dict -> do
  let convert :: forall v. Term (TermF id) v -> Term (TermF sid) v
      convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      typ' = InitialGoal (map (bimap convert convert) goals)
                         (Just $ mapDGraph convert dgraph)
                         (getFramework baseProblem)
      p'   = mkDPProblem typ' trs' dps'

  let (omegaConstraint, extraConstraintsAdded) = omega p'
  assertAll [omegaConstraint]
  assertAll [ l >~ r | l:->r <- rules dps']

  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  mapM_ (assertW 1 . (:[]) . not . input . usable) (Map.elems dict)

--  debug ("\nThe indexes are: " ++ show decreasing_dps) $
  return $ do
             decreasing <- decode decreasing_dps
             ec <- extraConstraintsAdded
             return ([ r | (r,False) <- zip [(0::Int)..] decreasing]
                    ,ec)
{-
    (weakly, strictly) <- do
       weakly   <- evalB (and $ omegaIG  p' :
                               [l >~ r | (False, l:->r) <- zip decreasing (rules dps')])
       strictly <- evalB (and [l > r | (True, l:->r) <- zip decreasing (rules dps')])
       return (weakly, strictly)

    (weaklyS, strictlyS) <- do
       weaklyS <- evalB (and $ omegaIG p' : [l >~ r | (False, l:->r) <- zip decreasing (rules dps')])

       strictlyS <- mapM evalB ([l > r | (True, l:->r) <- zip decreasing (rules dps')])

       return (weaklyS, strictlyS)


    verification <- verifyRPOAF typ' trs' dps' decreasing_dps
    let isValidProof
          | isCorrect verification = True
          | otherwise = pprTrace verification False

    CE.assert isValidProof $
-}

--    CE.assert  (null strictlyS) $
--     CE.assert (null weaklyS) $
--     CE.assert strictly $
--     CE.assert weakly $


rpoAF_NDP :: forall typ repr problem problem' trs trs' id tv v sid m.
         (problem  ~ Problem typ  trs
         ,problem' ~ Problem typ  trs'
         ,trs      ~ NarradarTRS (TermF id) tv
         ,trs'     ~ NarradarTRS (TermF sid) tv
         ,id       ~ Family.Id sid
         ,v        ~ Family.Var sid
         ,v        ~ Family.Var v
         ,TermF sid~ Family.TermF repr
         ,Ord tv
         ,Ord id, Show id, Pretty id
         ,Ord sid, Pretty sid
         ,MkDPProblem typ (NTRS sid)
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,RPOExtCircuit repr sid, CoRPO repr (TermF sid) tv v
         ,UsableSymbol sid
         ,SATSymbol sid
         ,MkDPProblem typ trs'
         ,Decode v Bool
         ,MonadSAT repr v m
         ,v ~ Var) =>
            Bool
         -> (problem' -> repr v)
         -> problem
         -> m (EvalM v ( ([Int], [Int]), BIEnv v, [sid]))
rpoAF_NDP allowCol omega p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      p'   = mkDPProblem (getFramework p) trs' dps'

  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  let af_ground_rhs_dps :: forall repr. (Circuit repr, Co repr v) => [repr v]
      af_ground_rhs_dps = map afGroundRHS (rules dps')
--      variable_cond     = and $ map variableCondition (rules dps')

  assert (map input decreasing_dps)
  assert af_ground_rhs_dps
-- FIXME reenable the variable condition
  -- assert variable_cond

  assertAll (omega p' :
             [ l >~ r | l:->r <- rules dps'])

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  mapM_ (assertW 1 . (:[]) . not . input . usable) (Map.elems dict)

  return $ do
    decreasing <- decode decreasing_dps
    af_ground  <- decode (af_ground_rhs_dps :: [Eval v])
    return ([ r | (r,False) <- zip [(0::Int)..] decreasing]
           ,[ r | (r,False) <- zip [(0::Int)..] af_ground])


runRPOAF allowCol sig f = do
  let ids  = arities sig
      bits = calcBitWidth $ Map.size ids

  (symbols, constraints) <- unzip <$> mapM mkSATSymbol (Map.toList ids)

  assertAll constraints

  if allowCol
    then assertAll [not(listAF s) --> one [inAF i s | i <- [1..a]]
                    | (s,a) <- zip symbols (Map.elems ids)]
    else assertAll (map listAF symbols)

  let dict       = Map.fromList (zip (Map.keys ids) symbols)
  mkRes <- f dict
  return $ do -- Debug.trace ("The symbols are:\n" ++ show symbols) $ do
    env <- ask
    res <- mkRes
    return (res, env, symbols)

-- ----------------------
-- Symbols set extensions
-- ----------------------

instance ( RPOCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr) =>
    RPOExtCircuit repr (Usable (RPOSsymbol v a)) where
     exEq s t ss tt =
       and [useMul s, useMul t, muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpeq s t ss tt]

     exGt s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt s t ss tt]

     exGe s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt \/ muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt s t ss tt \/ lexpeq s t ss tt]
{-
     exGe s t ss tt =
       and [useMul s, useMul t, mulge s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpge_exist s t ss tt]
-}

instance (RPOCircuit repr, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Ord a, Pretty a) =>
  RPOExtCircuit repr (Usable(LPOSsymbol v a)) where
  exEq s t = lexpeq s t
  exGt s t = lexpgt s t
--  exGe = lexpge_exist

instance (RPOCircuit repr, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Pretty a, Ord a) =>
  RPOExtCircuit repr (Usable(LPOsymbol v a)) where
  exEq s t = lexeq s t
  exGt s t = lexgt s t

instance (RPOCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Pretty a, Ord a) =>
  RPOExtCircuit repr (Usable(MPOsymbol v a)) where
  exEq s t = muleq s t
  exGt s t = mulgt s t

instance (RPOCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Pretty a, Ord a) =>
  RPOExtCircuit repr (Usable(RPOsymbol v a)) where
  exEq s t ss tt =
      and [ useMul s, useMul t, muleq s t ss tt]
      \/
      and [not$ useMul s, not$ useMul t, lexeq s t ss tt]

  exGt s t ss tt =
      and [useMul s, useMul t, mulgt s t ss tt]
      \/
      and [not$ useMul s, not$ useMul t, lexgt s t ss tt]

-- -------------------------
-- Narrowing related stuff
-- -------------------------
afGroundRHS (_ :-> t) = and  [ or [ not(inAF i f)
                                    | prefix <- tail $ inits pos
                                    , let Just f = rootSymbol (t ! init prefix)
                                    , let      i = last prefix]
                               | pos <- [noteV v | v <- vars(annotateWithPos t)]]

variableCondition rule@(_ :-> r)
                      = and  [ or [ not(inAF i f)
                                    | prefix <- tail $ inits pos
                                   , let Just f = rootSymbol (r ! init prefix)
                                    , let      i = last prefix]
                               | pos <- [noteV v | v <- extraVars(annotateWithPos <$> rule)]]


-- -----------------------------------
-- Lexicographic extension with AF
-- -----------------------------------

lexgt id_f id_g ff gg = go (zip (map input $ filtering_vv id_f) ff)
                           (zip (map input $ filtering_vv id_g) gg)
 where
  go :: [(repr var,Term termF tvar)] -> [(repr var,Term termF tvar)] -> repr var
  go []     _      = false
  go ff      []    = or [ af_f | (af_f,_) <- ff]
  go ((af_f,f):ff) ((af_g,g):gg)
    =  ite af_f
           (ite af_g
                ((f > g) \/ ((f ~~ g) /\ go ff gg))
                (go ((af_f,f):ff) gg))
           (go ff ((af_g,g):gg))

lexeq id_f id_g ff gg = go (zip (map input $ filtering_vv id_f) ff)
                           (zip (map input $ filtering_vv id_g) gg)
 where
  go :: [(repr var,Term termF tvar)] -> [(repr var,Term termF tvar)] -> repr var
  go []     []     = true
  go ff      []    = not $ or [ af_f | (af_f,_) <- ff]
  go []      gg    = not $ or [ af_g | (af_g,_) <- gg]
  go ((af_f,f):ff) ((af_g,g):gg)
    =  ite af_f
           (ite af_g
                ((f ~~ g) /\ go ff gg)
                (go ((af_f,f):ff) gg))
           (go ff ((af_g,g):gg))

lexgt_exist _    _    [] _  = false
lexgt_exist id_f _    ff [] = or . map input . filtering_vv $ id_f
lexgt_exist id_f id_g ff gg = (`runCont` id) $ do
-- We build a matrix M of dim n_f x n_g containing all
-- the comparisons between tails of ff and gg
-- That is, M[0,0] = lexgt ff gg
--          M[1,0] = lexgt (drop 1 ff) gg
--          M[0,1] = lexgt ff (drop 1 gg)
--          ...
-- Actually, the matrix containts additional elements
--          M[n_f+1, i] = value if we drop all the elements of ff and i elements of gg
--          M[i, n_g+1] = value if we drop all the elements of gg and i elements of ff
-- The proposition is true iff M[0,0] is true
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i, ff_i)  <-  (tails m `zip` tails (zip filters_f ff))
                      , (m_ij, gg_j) <-  (getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg))]

  return ( m!!0!!0 /\ and assertions)
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint _ []     _      = false
   constraint _ ff      []    = or [ af_f | (af_f,_) <- ff]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f>g \/ (f~~g /\ m!!1!!1))
                         (m!!0!!1))
                    (m!!1!!0)


lexgt_existA, lexpgt_existA, lexpge_existA, lexeq_existA ::
  forall id termF tv v repr .
                        (HasPrecedence id
                        ,HasFiltering id
                        ,HasStatus id
                        ,HasId termF
                        ,Foldable termF
                        ,Eq(Term termF tv)
                        ,id ~ Family.Id termF
--                        ,id ~ Family.Id repr
                        ,v  ~ Family.Var id
                        ,termF ~ Family.TermF repr
                        ,ECircuit repr
                        ,ExistCircuit repr
                        ,RPOCircuit repr
                        ,AssertCircuit repr
                        ,CoRPO repr termF tv v
                        ) =>
                        id -> id -> [Term termF tv] -> [Term termF tv] -> repr v
lexgt_existA _    _    [] _  = false
lexgt_existA id_f _    ff [] = or . map input . filtering_vv $ id_f
lexgt_existA id_f id_g ff gg = (`runCont` id) $ do
-- We build a matrix M of dim n_f x n_g containing all
-- the comparisons between tails of ff and gg
-- That is, M[0,0] = lexgt ff gg
--          M[1,0] = lexgt (drop 1 ff) gg
--          M[0,1] = lexgt ff (drop 1 gg)
--          ...
-- Actually, the matrix containts additional elements
--          M[n_f+1, i] = value if we drop all the elements of ff and i elements of gg
--          M[i, n_g+1] = value if we drop all the elements of gg and i elements of ff
-- The proposition is true iff M[0,0] is true
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i, ff_i)  <-  (tails m `zip` tails (zip filters_f ff))
                      , (m_ij, gg_j) <-  (getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg))]

  return $ assertCircuits assertions (head $ head m)
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint :: [[repr v]] -> [(repr v,Term termF tv)] -> [(repr v,Term termF tv)] -> repr v
   constraint _ []     _      = false
   constraint _ ff      []    = or [ af_f | (af_f,_) <- ff]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f>g \/ (f~~g /\ m!!1!!1))
                         (m!!0!!1))
                    (m!!1!!0)

lexeq_exist _    _    [] [] = true
lexeq_exist id_f _    _  [] = not . or . map input . filtering_vv $ id_f
lexeq_exist _    id_g [] _  = not . or . map input . filtering_vv $ id_g
lexeq_exist id_f id_g ff gg = (`runCont` id) $ do
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i,  ff_i) <- tails m `zip` tails (zip filters_f ff)
                      , (m_ij, gg_j) <- getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg)]

  return ( m!!0!!0 /\ and assertions)
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint _ []     []     = true
   constraint _ ff      []    = not $ or [ af_f | (af_f,_) <- ff]
   constraint _ []      gg    = not $ or [ af_g | (af_g,_) <- gg]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f~~g /\ m!!1!!1)
                         (m!!0!!1))
                    (m!!1!!0)

--lexeq_existA _    _    [] [] = true
--lexeq_existA id_f _    _  [] = not . or . map input . filtering_vv $ id_f
--lexeq_existA _    id_g [] _  = not . or . map input . filtering_vv $ id_g
lexeq_existA id_f id_g ff gg = (`runCont` id) $ do
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i,  ff_i) <- tails m `zip` tails (zip filters_f ff)
                      , (m_ij, gg_j) <- getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg)]

  return ( assertCircuits assertions (head $ head m) )
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint :: [[repr v]] -> [(repr v,Term termF tv)] -> [(repr v,Term termF tv)] -> repr v
   constraint _ []     []     = true
   constraint _ ff      []    = not $ or [ af_f | (af_f,_) <- ff]
   constraint _ []      gg    = not $ or [ af_g | (af_g,_) <- gg]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f~~g /\ m!!1!!1)
                         (m!!0!!1))
                    (m!!1!!0)

lexpeq, lexpgt, lexeq, lexgt, muleq,mulgt,mulge ::
         forall id termF repr tvar var .
         ( var   ~ Family.Var id
         , id    ~ Family.Id termF
         , termF ~ Family.TermF repr
         , HasId termF, Foldable termF
         , HasFiltering id, HasStatus id, HasPrecedence id
         , Eq (Term termF tvar), Eq id
         , RPOCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         , CoRPO repr termF tvar var
         ) => id -> id -> [Term termF tvar] -> [Term termF tvar] -> repr var


--lexpeq :: (ECircuit repr, RPOCircuit repr (Symbol a)) =>
--          Symbol a -> Symbol a -> [TermN (Symbol a)] -> [TermN (Symbol a)] -> repr Var
--lexpeq id_f id_g ss tt | pprTrace (text "encoding " <+> ss <+> text "~" <+> tt) False = undefined
lexpeq id_f id_g ss tt =
  eqArity /\
  and ( [ (f_ik /\ g_jk) --> s_i ~~ t_j
              | (s_i, f_i) <- zip ss ff
              , (t_j, g_j) <- zip tt gg
              , (f_ik, g_jk) <- zip f_i g_j])
    where
       (Just ff, Just gg) = (lexPerm id_f, lexPerm id_g)
       eqArity = and ( take m (zipWith (<-->) (map or ff ++ repeat false)
                                              (map or gg ++ repeat false))
                     )
       m   = max (length ff) (length gg)

--lexpgt id_f id_g ss tt | pprTrace (text "encoding " <+> ss <+> text ">" <+> tt) False = undefined
lexpgt id_f id_g ss tt = expgt_k (transpose $ enc_f) (transpose $ enc_g)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g
       n = length ss
       m = length tt
       expgt_k [] _ = false
       expgt_k (f_k:_) [] = or f_k
       expgt_k (f_k:ff) (g_k:gg)
         = or [f_ik /\ and [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ expgt_k ff gg))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

lexpgt_exist id_f id_g [] _  = false
lexpgt_exist id_f id_g ss tt = (`runCont` id) $ do
  let k = min (length ss) (length tt) + 1
  vf_k <- replicateM k (cont existsBool)
  let constraints = zipWith3 expgt_k (transpose $ enc_f) (transpose $ enc_g) (tail vf_k) ++
                    [the_tail]
      the_tail = if length ss P.> length tt
                   then or (transpose enc_f !! length tt)
                   else false

  let assertions = zipWith (<-->) vf_k constraints
  return (head vf_k /\ and assertions)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g

       expgt_k f_k g_k next
         = or [f_ik /\ and [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ next))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

lexpgt_existA id_f id_g [] _  = false
lexpgt_existA id_f id_g ss tt = (`runCont` id) $ do
  let k = min (length ss) (length tt) + 1
  vf_k <- replicateM k (cont existsBool)
  let constraints = zipWith3 expgt_k (transpose $ enc_f) (transpose $ enc_g) (tail vf_k) ++
                    [the_tail]
      the_tail = if length ss P.> length tt
                   then or (transpose enc_f !! length tt)
                   else false

  let assertions = zipWith (<-->) vf_k constraints
  return (assertCircuits assertions $ head vf_k)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g

       expgt_k f_k g_k next
         = or [f_ik /\ and [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ next))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

lexpge_existA id_f id_g ss tt = (`runCont` id) $ do
  let k = min (length ss) (length tt) + 1
  vf_k <- replicateM k (cont existsBool)
  let constraints = zipWith3 expge_k (transpose $ enc_f) (transpose $ enc_g) (tail vf_k) ++
                    [the_tail]
      the_tail = if length ss P.> length tt
                   then eqArity \/ or (enc_f !! length tt)
                   else eqArity

  let assertions = zipWith (<-->) vf_k constraints
  return (assertCircuits assertions $ head vf_k)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g

       expge_k f_k g_k next
         = or [f_ik /\ and [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ next))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

       m = max (length enc_f) (length enc_g)
       eqArity = and ( take m (zipWith (<-->) (map or enc_f ++ repeat false)
                                              (map or enc_g ++ repeat false))
                     )



-- ---------------------------
-- Multiset extension with AF
-- ---------------------------
mulge id_f id_g [] gg = none $ map (`inAF` id_g) [1..length gg]
mulge id_f id_g ff gg = mulgen id_f id_g ff gg (const true)

mulgt id_f id_g []  _   = false
mulgt id_f id_g ff  gg  =
    mulgen id_f id_g ff gg (\epsilons ->
                                not $ and [inAF i id_f --> ep_i
                                           | (i, ep_i) <- zip [1..] epsilons])

muleq id_f id_g [] [] = true
muleq id_f id_g [] gg = none $ map (`inAF` id_g) [1..length gg]
muleq id_f id_g ff gg =
    mulgen id_f id_g ff gg (\epsilons ->
                                and [inAF i id_f --> ep_i
                                      | (i, ep_i) <- zip [1..] epsilons])


mulgen:: ( var   ~ Family.Var id
         , id    ~ Family.Id termF
         , termF ~ Family.TermF repr
         , HasFiltering id, HasStatus id, HasPrecedence id
         , HasId termF, Foldable termF, Eq (Term termF tvar), Eq id
         , RPOCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         , CoRPO repr termF tvar var
         ) => id -> id -> [Term termF tvar] -> [Term termF tvar] -> ([repr var] -> repr var) ->  repr var
mulgen id_f id_g ff gg k = (`runCont` id) $ do
    let (i,j)    = (length ff, length gg)

    epsilons  <- replicateM i (cont existsBool)
    gammasM_t <- replicateM i $ replicateM j (cont existsBool)
    let gammasM = transpose gammasM_t

        oneCoverForNonFilteredSubtermAndNoCoverForFilteredSubterms =
          [ ite (inAF j id_g)
                (one  gammas_j)
                (none gammas_j)
            | (j, gammas_j) <- zip [1..] gammasM ]

        filteredSubtermsCannotCover =
          [ not(inAF i id_f) --> none gammas_i
            | (i, gammas_i) <- zip [1..] gammasM_t]

        subtermUsedForEqualityMustCoverOnce =
          [ ep_i --> one gamma_i
            | (ep_i, gamma_i) <- zip epsilons gammasM_t]

        greaterOrEqualMultisetExtension =
          [ gamma_ij --> ite ep_i (f_i ~~ g_j)
                                  (f_i >  g_j)
                  | (ep_i, gamma_i, f_i) <- zip3 epsilons gammasM_t ff
                  , (gamma_ij, g_j)      <- zip  gamma_i gg]
    return $
       and ( k epsilons
           : oneCoverForNonFilteredSubtermAndNoCoverForFilteredSubterms
          ++ filteredSubtermsCannotCover
          ++ subtermUsedForEqualityMustCoverOnce
          ++ greaterOrEqualMultisetExtension
           )

-- ------------------------
-- Usable Rules with AF
-- ------------------------
omegaNone p =  and ([ l >~ r | l:->r <- rules (getR p)] ++
                    [ iusable f | f <- Set.toList $ getDefinedSymbols (getR p)])

omegaUsable p = -- pprTrace ("Solving P=" <> getP p $$ "where dd = " <> dd) $
            and ([go r trs | _:->r <- dps] ++
                 [iusable f --> and [ l >~ r | l:->r <- rulesFor f trs]
                   | f <- Set.toList dd ] ++
                 [not(iusable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                )

   where
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd = getDefinedSymbols $ getR (iUsableRules p (rhs <$> dps))

    go (Pure x) _ = and $ map iusable $ toList $ getDefinedSymbols (iUsableRulesVar p x)

    go t trs
      | id_t `Set.notMember` dd
      = and [ inAF i id_t --> go t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = iusable id_t /\
        and ([ go r rest | _:->r <- rls ] ++
             [ inAF i id_t --> go t_i rest
                | (i, t_i) <- zip [1..] tt ]
            )
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls -- :: [Rule t Var]

omegaNeeded p = pprTrace (text "Solving P=" <+> getP p $$ text "where dd = " <+> dd) $
            and ([go r trs | _:->r <- dps] ++
                 [iusable f --> and [ l >~ r | l:->r <- rulesFor f trs]
                   | f <- Set.toList dd ]  ++
                 [not(iusable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                )

   where
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd
       | getMinimalityFromProblem p == M = getDefinedSymbols $ getR (neededRules p (rhs <$> dps))
       | otherwise                       = getDefinedSymbols $ getR (iUsableRules p (rhs <$> dps))

    go (Pure x) _
       | getMinimalityFromProblem p == M = true
       | otherwise                       = and $ map iusable $ toList $ getDefinedSymbols (iUsableRulesVar p x)

    go t trs
      | id_t `Set.notMember` dd
      = and [ inAF i id_t --> go t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = iusable id_t /\
        and ([ go r rest | _:->r <- rls ]++
             [ inAF i id_t --> go t_i rest
                | (i, t_i) <- zip [1..] tt ]
            )
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls -- :: [Rule t Var]

omegaIG p = --pprTrace ("Solving P=" <> getP p $$ "where the involved pairs are: " <> ip $$ text "and dd=" <+> dd ) $
           (and ([go l r trs | l:->r <- ip] ++
                 [iusable f --> and [ l >~ r | l:->r <- rulesFor f trs]
                    | f <- Set.toList dd ] ++
                 [not(iusable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                )
           ,return [])

   where
    ip = forDPProblem involvedPairs p
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd
       | M <- getMinimalityFromProblem p = getDefinedSymbols $ getR (neededRules p (rhs <$> dps))
       | otherwise                       = getDefinedSymbols (reachableUsableRules p)

    go l (Pure x) _ =
      -- If there is an extra variable, everything is usable
        every poss (\p -> or [ not(inAF i f)
                              | n <- [0..length p - 1]
                              , let (pre, i:_) = splitAt n p
                              , let f = fromMaybe (error "omega: fromJust") $
                                        rootSymbol (l!pre)])
         --> and(map iusable $ toList $ getDefinedSymbols (getR p))

     where
      poss = occurrences (Pure x) l

    go l t trs
      | id_t `Set.notMember` dd
      = and [ inAF i id_t --> go l t_i trs
               | (i, t_i) <- zip [1..] tt ]
      | otherwise
      = and (  iusable id_t
            :  [ go l' r' rest | l':->r' <- rls ]
            ++ [ inAF i id_t --> go l t_i rest
                   | (i, t_i) <- zip [1..] tt ]
            )
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls

omegaIGgen :: forall problem initialgoal id base repr v.
              (problem ~ NProblem initialgoal id
              ,initialgoal ~ InitialGoal (TermF id) base
              ,Var ~ Family.Var id
              ,Traversable (Problem base), MkDPProblem base (NTRS id), HasMinimality base
              ,NCap base id
              ,NUsableRules base id
              ,NNeededRules base id
              ,Pretty base
              ,Ord id, Pretty id, Show id, Hashable id, DPSymbol id, GenSymbol id
              ,HasStatus id
              ,HasFiltering id
              ,HasPrecedence id
              ,UsableSymbol id
              ) => problem -> (Tree (TermN id) Var, EvalM Var [Tree (TermN id) Var])
omegaIGgen p
  | isLeftLinear (getR p) = pprTrace ("omegaIGgen: partial = " <+> partial)
                            omegaIG p
  | (omegaConstraint,extra1) <- omegaIG p
  = (omegaConstraint /\ (iusable gen --> and extraConstraints)
    ,do { e1 <- extra1;
          b  <- decode (isEval $ iusable gen);
          return $
           if b then (e1 ++ extraConstraints)
                else []
        })
 where
   isTree = id :: forall term var. Tree term var -> Tree term var
   isEval = id :: forall var. Eval var -> Eval var
   Just gen = find isGenSymbol (toList $ getDefinedSymbols p)
--   genTerm :: Term (TermF id) Narradar.Var
   genTerm = term gen []
--   extraConstraints :: forall repr. (RPOExtCircuit repr id, CoRPO repr (TermF id) Var) => [repr Var]
   extraConstraints = [ genTerm > term f (replicate i genTerm) | (f,i) <- Map.toList partial]
   partial = definedSymbols (getSignature p)
             `Map.difference`
             Map.fromList
             [(f, arity ) | l :-> r <- rules (getR p)
                          , Just f <- [rootSymbol l]
                          , isLinear l && P.all isVar (properSubterms l)
                          , let arity = length (properSubterms l)]

rulesFor :: (HasId t, Family.Id t ~ id, Eq id) => id -> [Rule t v] -> [Rule t v]
rulesFor f trs = [ l:->r | l:-> r <- trs, rootSymbol l == Just f ]

-- --------
-- Testing
-- --------

verifyRPOAF :: ( rule ~ RuleF term
               , term ~ Term (TermF id) var
               , rule ~ Family.Rule trs
               , id   ~ Family.Id trs
               , var  ~ Family.Var trs
               , var  ~ Family.Var id
               , var  ~ Family.Var var
               , TermF id ~ Family.TermF trs
--               , Narradar.Var ~ var
               , Enum var, Ord var, GetVars var, Hashable var, Show var, Rename var
               , Decode var Bool
               , AF.ApplyAF term
               , HasRules trs, HasSignature trs, AF.ApplyAF trs, GetVars trs
               , Ord id, UsableSymbol id, Pretty id, Show id
               , HasPrecedence id, HasStatus id, HasFiltering id
               , IUsableRules typ trs
               ) =>
               typ -> trs -> trs -> [Int] -> EvalM var (VerifyRPOAF rule)
verifyRPOAF typ the_rules the_pairs nonDecPairsIx = do

  theAf <- AF.fromList' `liftM` mapM getFiltering (toList $ getAllSymbols signature)
  let theFilteredPairs = rules $ AF.apply theAf the_pairs

  let theWeakPairs = CE.assert (P.all (P.< npairs) nonDecPairsIx) $
                     selectSafe "verifyRPOAF 1" nonDecPairsIx (rules the_pairs)
      theDecPairs  = selectSafe "verifyRPOAF 2" ([0..npairs - 1] \\ nonDecPairsIx) (rules the_pairs)

  theUsableRules <- liftM Set.fromList $ runListT $ do
                       l:->r <- msum $ map return $ rules the_rules
                       let Just id = rootSymbol l
                       guard =<< lift (evalDecode $ input $ usable id)
                       return (l:->r)

  let expectedUsableRules =
        Set.fromList
         [ rule
         | let urAf = Set.fromList $
                      rules(iUsableRules3 typ the_rules the_pairs (rhs <$> theFilteredPairs))
         , rule <- rules the_rules
         , AF.apply theAf rule `Set.member` urAf]

  falseDecreasingPairs <- runListT $ do
     s:->t <- li theDecPairs
     guard =<< lift (evalDecode $ not(s > t))
     return (s:->t)

  falseWeaklyDecreasingPairs <- runListT $ do
     s:->t <- li theWeakPairs
     guard =<< lift (evalDecode $ not( s >~  t))
     return (s:->t)

  falseWeaklyDecreasingRules <- runListT $ do
     s:->t <- li (toList theUsableRules)
     guard =<< lift (evalDecode $ not( s >~  t))
     return (s:->t)

  let missingUsableRules = [] -- toList (Set.difference expected_usableRules the_usableRules)
      excessUsableRules  = [] -- toList (Set.difference the_usableRules expected_usableRules)

  return VerifyRPOAF{thePairs = rules the_pairs, ..}

 where
  signature = getSignature (the_rules `mappend` the_pairs)

  getFiltering s = do
    isListAF   <- evalDecode $ listAF s
    filterings <- mapM decode (filtering_vv s)
    let positions = [ i | (i,True) <- zip [1..(getArity signature s)] filterings]
    return $ if isListAF
              then (s, Right positions)
              else case positions of
                     [p] -> (s, Left p)
                     _   -> error ("Invalid collapsing filtering " ++ show positions ++
                                   " for symbol " ++ show (pPrint s))

  npairs    = length (rules the_pairs)
