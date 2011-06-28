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

module Narradar.Constraints.SAT.RPOAF (
   SATSymbol(..), SymbolRes(..)
  ,RPOSsymbol(..), RPOsymbol(..), LPOsymbol(..), LPOSsymbol(..), MPOsymbol(..)
  ,rpoAF_DP, rpoAF_NDP, rpoAF_IGDP
  ,rpo, rpos, lpo, lpos, mpo
  ,verifyRPOAF, isCorrect
  ,omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone
  ) where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Reader
import qualified Control.RMonad as R
import qualified Data.Array as A
import Data.Bifunctor
import Data.Foldable (Foldable, foldMap, toList)
import Data.List ((\\), find, transpose, inits, tails, zip4)
import Data.Maybe
import Data.Monoid
import Data.Hashable
import Data.Traversable (traverse)
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse)
import Narradar.Framework.Ppr as Ppr

import Narradar.Constraints.Syntactic
import Narradar.Constraints.SAT.MonadSAT
import Narradar.Constraints.SAT.RPOAF.Symbols
import Narradar.Framework
import Narradar.Types.DPIdentifiers
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Problem
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGen
import Narradar.Utils
import Narradar.Types.ArgumentFiltering (AFId)

import qualified Funsat.ECircuit as ECircuit
import qualified Narradar.Constraints.RPO as RPO
import qualified Narradar.Types as Narradar
import qualified Narradar.Types.ArgumentFiltering as AF
import qualified Prelude as P
import Prelude hiding (catch, lex, not, and, or, any, all, quot, (>))

class SATSymbol sid where
  mkSATSymbol :: (Decode v Bool v, Show id, MonadSAT repr v m) =>
                 (id, Int, Bool) -> m (sid v id)

instance SATSymbol RPOSsymbol where mkSATSymbol = rpos
instance SATSymbol RPOsymbol  where mkSATSymbol = rpo
instance SATSymbol LPOSsymbol where mkSATSymbol = lpos
instance SATSymbol LPOsymbol  where mkSATSymbol = lpo
instance SATSymbol MPOsymbol  where mkSATSymbol = mpo

-- | RPO + AF

rpoAF allowCol trs = runRPOAF allowCol (getSignature trs) $ \dict -> do
  let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  let problem = and [ l > r | l:->r <- symb_rules]
  assert [problem]
  return (return ())


-- | Returns the indexes of non decreasing pairs and the symbols used
rpoAF_DP allowCol omega p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs'    = mapNarradarTRS convert (getR p)
      dps'    = mapNarradarTRS convert (getP p)
      p'      = mkDPProblem (getFramework p) trs' dps'

  decreasing_dps <- replicateM (length $ rules dps') boolean

  assertAll [omega p']
  assertAll [ l >~ r | l:->r <- rules dps']

  assertAll [(l > r) <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]
  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  mapM_ (assertW 1 . (:[]) . not . input . usable) (Map.elems dict)

  return $ do
    decreasing <- decode decreasing_dps
    let the_non_decreasing_pairs = [ r | (r,False) <- zip [(0::Int)..] decreasing]
    return the_non_decreasing_pairs


rpoAF_IGDP :: (Ord id
              ,Traversable (Problem base), Pretty base
              ,MkDPProblem (InitialGoal (TermF sid) base) (NTRS sid)
              ,NUsableRules base sid
              ,NCap base sid
--              ,NeededRules (TermF sid) Narradar.Var base (NTRS sid)
              ,HasMinimality base
              ,DPSymbol id, Pretty id
              ,SATSymbol satSymbol
              ,sid ~ satSymbol Var id
              ,Ord sid, Pretty sid, Show id
              ,UsableSymbol Var sid
              ,DPSymbol sid
              ,HasPrecedence Var sid
              ,HasStatus Var sid
              ,HasFiltering Var sid
              ,Hashable sid
              ,Decode sid (SymbolRes id) Var
              ,MonadSAT repr Var m
              ,RPOExtCircuit repr sid Narradar.Var
              ,HasSignature (NProblem (InitialGoal (TermF id) base) id)
              ) => Bool -> (NProblem (InitialGoal (TermF sid) base) sid -> (repr Var, EvalM Var extraConstraints))
                -> NProblem (InitialGoal (TermF id) base) id
                -> m (EvalM Var (([Int], extraConstraints), BIEnv Var, [sid]))

rpoAF_IGDP allowCol omega p@InitialGoalProblem{..}
  = runRPOAF allowCol (getSignature p `mappend` getSignature (pairs dgraph)) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      typ' = InitialGoal (map (bimap convert convert) goals)
                         (Just $ mapDGraph convert dgraph)
                         (getFramework baseProblem)
      p'   = mkDPProblem typ' trs' dps'

  let (omegaConstraint, extraConstraintsAdded) = omega p'
  assertAll ( omegaConstraint : [ l >~ r | l:->r <- rules dps'])

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

 where isTheRightKind :: InitialGoal (f id) base -> InitialGoal (f id) base
       isTheRightKind = id

rpoAF_NDP allowCol omega p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      p'   = mkDPProblem (getFramework p) trs' dps'

  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  let af_ground_rhs_dps = map afGroundRHS (rules dps')
      variable_cond     = and $ map variableCondition (rules dps')

  assert (map input decreasing_dps)
  assert af_ground_rhs_dps
  assertAll (omega  p' :
             [ l >~ r | l:->r <- rules dps'])

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  mapM_ (assertW 1 . (:[]) . not . input . usable) (Map.elems dict)

  return $ do
    decreasing <- decode decreasing_dps
    af_ground  <- decode (af_ground_rhs_dps :: [Eval Var])
    return ([ r | (r,False) <- zip [(0::Int)..] decreasing]
           ,[ r | (r,False) <- zip [(0::Int)..] af_ground])


runRPOAF allowCol sig f = do
  let ids  = getArities sig
      bits = calcBitWidth $ Map.size ids

  symbols <- mapM mkSATSymbol
                  [ (f, ar, def)
                    | (f,ar) <-  Map.toList ids
                    , let def = Set.member f (getDefinedSymbols sig)]
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

instance ( RPOCircuit repr (RPOSsymbol v a) tvar, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Ord tvar, Pretty tvar, Show tvar, Hashable tvar, Ord a, Pretty a) =>
    RPOExtCircuit repr (RPOSsymbol v a) tvar where
     exEq s t ss tt =
       and [useMul s, useMul t, muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpeq s t ss tt]

     exGt s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt_existA s t ss tt]

     exGe s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt \/ muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt_existA s t ss tt \/ lexpeq s t ss tt]
{-
     exGe s t ss tt =
       and [useMul s, useMul t, mulge s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpge_exist s t ss tt]
-}
instance (RPOCircuit repr (LPOSsymbol v a) tvar, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr, Ord a, Pretty a
         ,Ord tvar, Pretty tvar, Show tvar, Hashable tvar) =>
  RPOExtCircuit repr (LPOSsymbol v a) tvar where
  exEq s t = lexpeq s t
  exGt s t = lexpgt_existA s t
--  exGe = lexpge_exist

instance (RPOCircuit repr (LPOsymbol v a) tvar, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Ord a, Ord tvar, Pretty tvar, Show tvar, Hashable tvar) =>
  RPOExtCircuit repr (LPOsymbol v a) tvar where
  exEq s t = lexeq_existA s t
  exGt s t = lexgt_existA s t

instance (RPOCircuit repr (MPOsymbol v a) tvar, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr, Ord a
         ,Ord tvar, Pretty tvar, Show tvar, Hashable tvar) =>
  RPOExtCircuit repr (MPOsymbol v a) tvar where
  exEq s t = muleq s t
  exGt s t = mulgt s t

instance (RPOCircuit repr (RPOsymbol v a) tvar, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr, Ord a
         ,Ord tvar, Pretty tvar, Show tvar, Hashable tvar) =>
  RPOExtCircuit repr (RPOsymbol v a) tvar where
  exEq s t ss tt =
      and [ useMul s, useMul t, muleq s t ss tt]
      \/
      and [not$ useMul s, not$ useMul t, lexeq_existA s t ss tt]

  exGt s t ss tt =
      and [useMul s, useMul t, mulgt s t ss tt]
      \/
      and [not$ useMul s, not$ useMul t, lexgt_existA s t ss tt]

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
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont exists)
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
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont exists)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i, ff_i)  <-  (tails m `zip` tails (zip filters_f ff))
                      , (m_ij, gg_j) <-  (getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg))]

  return $ assertCircuits assertions (m!!0!!0)
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

lexeq_exist _    _    [] [] = true
lexeq_exist id_f _    _  [] = not . or . map input . filtering_vv $ id_f
lexeq_exist _    id_g [] _  = not . or . map input . filtering_vv $ id_g
lexeq_exist id_f id_g ff gg = (`runCont` id) $ do
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont exists)
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

lexeq_existA _    _    [] [] = true
lexeq_existA id_f _    _  [] = not . or . map input . filtering_vv $ id_f
lexeq_existA _    id_g [] _  = not . or . map input . filtering_vv $ id_g
lexeq_existA id_f id_g ff gg = (`runCont` id) $ do
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont exists)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i,  ff_i) <- tails m `zip` tails (zip filters_f ff)
                      , (m_ij, gg_j) <- getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg)]

  return ( assertCircuits assertions (m!!0!!0) )
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
  vf_k <- replicateM k (cont exists)
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
  vf_k <- replicateM k (cont exists)
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
  vf_k <- replicateM k (cont exists)
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


mulgen id_f id_g ff gg k = (`runCont` id) $ do
    let (i,j)    = (length ff, length gg)

    epsilons  <- replicateM i (cont exists)
    gammasM_t <- replicateM i $ replicateM j (cont exists)
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

omegaNeeded p = -- pprTrace ("Solving P=" <> getP p $$ "where dd = " <> dd) $
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

omegaIGgen p
  | isLeftLinear (getR p) = pprTrace ("omegaIGgen: partial = " <+> partial)
                            omegaIG p
  | (omegaConstraint,extra1) <- omegaIG p
  = (omegaConstraint /\ (iusable gen --> and extraConstraints)
    ,do { e1 <- extra1;
          b  <- decode (iusable gen :: Eval Var);
          return $
           if b then (e1 ++ map isTree extraConstraints)
                else []
        })
 where
   isTree = id :: Tree id v Var -> Tree id v Var
   Just gen = find isGenSymbol (toList $ getDefinedSymbols p)
   genTerm = term gen []
   extraConstraints = [ genTerm > term f (replicate i genTerm) | (f,i) <- Map.toList partial]
   partial = definedSymbols (getSignature p)
             `Map.difference`
             Map.fromList
             [(f, arity ) | l :-> r <- rules (getR p)
                          , Just f <- [rootSymbol l]
                          , isLinear l && P.all isVar (properSubterms l)
                          , let arity = length (properSubterms l)]

rulesFor :: (HasId t, TermId t ~ id, Eq id) => id -> [Rule t v] -> [Rule t v]
rulesFor f trs = [ l:->r | l:-> r <- trs, rootSymbol l == Just f ]

-- --------------------------------------
-- Support for Goal-problems identifiers
-- --------------------------------------

instance (Show a, GenSymbol a) => GenSymbol (RPOSsymbol Var a) where
    genSymbol = Symbol{ theSymbol    = genSymbol
                      , encodePrec   = V 10
                      , encodeUsable = V 11
                      , encodeAFlist = V 12
                      , encodeAFpos  = []
                      , encodePerm   = []
                      , encodeUseMset= V 13
                      , decodeSymbol = mkSymbolDecoder genSymbol (Natural $ V 10) (V 11) (V 12) [] [] (V 13)
                      }
    goalSymbol = Symbol{ theSymbol    = genSymbol
                       , encodePrec   = error "RPOAF.Symbol : goalSymbol"
                       , encodeUsable = error "RPOAF.Symbol : goalSymbol"
                       , encodeAFlist = error "RPOAF.Symbol : goalSymbol"
                       , encodeAFpos  = error "RPOAF.Symbol : goalSymbol"
                       , encodePerm   = []
                       , encodeUseMset= error "RPOAF.Symbol : goalSymbol"
                       , decodeSymbol = return (SymbolRes goalSymbol 0 False (Lex Nothing) (Right []))
                       }
    isGenSymbol  = isGenSymbol  . theSymbol
    isGoalSymbol = isGoalSymbol . theSymbol

deriving instance (Show a, GenSymbol a) => GenSymbol (LPOsymbol  Var a)
deriving instance (Show a, GenSymbol a) => GenSymbol (LPOSsymbol Var a)
deriving instance (Show a, GenSymbol a) => GenSymbol (MPOsymbol  Var a)
deriving instance (Show a, GenSymbol a) => GenSymbol (RPOsymbol  Var a)

-- --------
-- Testing
-- --------

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
