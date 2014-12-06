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
{-# LANGUAGE Rank2Types #-}

module Narradar.Constraints.SAT.RPOAF (
   UsableSymbolRes(..), prec, filtering, status, theSymbolR
  ,MkSATSymbol, RPOSsymbol(..), RPOsymbol(..), LPOsymbol(..), LPOSsymbol(..), MPOsymbol(..)
  ,RPOProblemN, RPOId
  ,rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, rpoAF_IGDP'
  ,rpo, rpos, lpo, lpos, mpo
  ,verifyRPOAF, isCorrect
  ,omegaUsable, omegaNeeded, omegaIG, omegaIGgen, omegaNone
  ,Usable, UsableSymbol(..), usableSymbol
  ) where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Free (Free(..))
import Control.Monad.List
import Control.Monad.Reader
import Data.Bifunctor
import Data.Functor1
import Data.Foldable (Foldable, toList)
import Data.List ((\\), find, transpose, inits, tails)
import Data.Maybe
import Data.Monoid
import Data.Hashable
import Data.Traversable (Traversable, traverse)
import Data.Typeable (Typeable)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Funsat.TermCircuit.RPO.Symbols as Funsat
import Funsat.Circuit (CastCircuit, CastCo)
import Funsat.TermCircuit (Co, CoTerm, assertCircuits)
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.RPO ()
import Funsat.TermCircuit.RPO.Symbols (Natural(..), LPOSsymbol(..), LPOsymbol(..), MPOsymbol(..), RPOSsymbol(..), RPOsymbol(..), mkSymbolDecoder)

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
import Narradar.Utils hiding (none)

import qualified Data.Term.Family as Family
import qualified Narradar.Types.ArgumentFiltering as AF
import qualified Prelude as P
import Prelude hiding (lex, not, and, or, any, all, quot, (>))
import qualified Debug.Trace as Debug

import Debug.Hoed.Observe
import Control.DeepSeq (NFData)

-- TODO apply these constraint synonyms consistently across this file
type RPOId id = (FrameworkId id, UsableSymbol id, HasPrecedence id, HasStatus id, HasFiltering id, DPSymbol id)
type RPOProblemN typ id = (FrameworkProblemN typ id, RPOId id, NeededRules (NProblem typ id))

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
         ,Pretty sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,TermExtCircuit repr sid, CoTerm repr (TermF sid) tv v
         ,Decode v Bool
         ,MonadReader r mr
         ,MonadSAT repr v m
         ,v ~ Var) =>
         Bool -> MkSATSymbol sid -> trs -> m( mr ((), r, [sid]))
rpoAF allowCol mkS trs = runRPOAF allowCol mkS (getSignature trs) $ \dict -> do
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
         ,Ord tv, Observable tv
         ,Functor1 typ
         ,IsDPProblem (typ (TermF id))
         ,MkDPProblem (typ (TermF sid)) trs'
         ,FrameworkId sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,HasSignature (Problem (typ (TermF id)) trs)
         ,TermExtCircuit repr sid, CoTerm repr (TermF sid) tv v
         ,UsableSymbol sid
         ,Decode v Bool
         ,MonadSAT repr v m
         ,v ~ Var) =>
         Bool ->
         MkSATSymbol sid ->
         (Problem (typ (TermF sid)) trs' -> repr v) -> Problem (typ (TermF id)) trs
         -> m (EvalM v ([Int], BIEnv v, [sid]))

rpoAF_DP allowCol mkS omega p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF allowCol mkS (getSignature p) $ \dict -> do
  let convert = mapTermSymbols f_id
      f_id    = (\f -> fromMaybe (error ("rpoAF_DP: Symbol not found " ++ show( f))) $ Map.lookup f dict)
      trs'    = fmap convert (getR p)
      dps'    = fmap convert (getP p)
      typ'    = fmap1 (bimap f_id id) $ getFramework p
      p'      = mkDPProblem typ' trs' dps'

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


rpoAF_IGDP :: forall initialgoal initialgoal' problem problem' trs trs' id sid repr m base extraConstraints.
         (initialgoal  ~ InitialGoal (TermF id) base
         ,initialgoal' ~ InitialGoal (TermF sid) base
         ,problem  ~ Problem initialgoal trs
         ,problem' ~ Problem initialgoal' trs'
         ,trs      ~ NTRS id
         ,trs'     ~ NTRS sid
         ,id       ~ Family.Id sid
         ,Var      ~ Family.Var sid
         ,TermF sid~ Family.TermF repr
         ,FrameworkId id
         ,FrameworkId sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,UsableSymbol sid
         ,TermExtCircuit repr sid, CoTerm repr (TermF sid) Narradar.Var Var
         ,CastCircuit repr repr, CastCo repr repr Var
         ,Traversable (Problem base), Pretty base
         ,MkDPProblem initialgoal' (NTRS sid)
         ,IsDPProblem base
         ,MkDPProblem initialgoal' trs'
         ,MonadSAT repr Var m
         ,Observable (TermN id)
         ) =>
            Bool
         -> MkSATSymbol sid
         -> (problem' -> (repr Var, EvalM Var [Tree (TermN sid) Var]))
         -> problem
         -> m (EvalM Var ( ([Int], [Tree (TermN id) Var]), BIEnv Var, [sid]))
rpoAF_IGDP = rpoAF_IGDP'

rpoAF_IGDP' :: forall initialgoal initialgoal' problem problem' trs trs' id sid repr repr' m base extraConstraints.
         (initialgoal  ~ InitialGoal (TermF id) base
         ,initialgoal' ~ InitialGoal (TermF sid) base
         ,problem  ~ Problem initialgoal trs
         ,problem' ~ Problem initialgoal' trs'
         ,trs      ~ NTRS id
         ,trs'     ~ NTRS sid
         ,id       ~ Family.Id sid
         ,Var      ~ Family.Var sid
         ,TermF sid~ Family.TermF repr
         ,FrameworkId id
         ,FrameworkId sid
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,UsableSymbol sid
         ,TermExtCircuit repr sid, CoTerm repr (TermF sid) Narradar.Var Var
         ,CastCircuit repr' repr, CastCo repr' repr Var
         ,Traversable (Problem base), Pretty base
         ,MkDPProblem initialgoal' (NTRS sid)
         ,IsDPProblem base
         ,MkDPProblem initialgoal' trs'
--         ,Decode sid (SymbolRes id) v
         ,MonadSAT repr Var m
         ,Observable (TermN id)
         ) =>
            Bool
         -> MkSATSymbol sid
         -> (problem' -> (repr' Var, EvalM Var [Tree (TermN sid) Var]))
         -> problem
         -> m (EvalM Var ( ([Int], [Tree (TermN id) Var]), BIEnv Var, [sid]))

rpoAF_IGDP' allowCol mkS omega p@InitialGoalProblem{..}
  = runRPOAF allowCol mkS (getSignature p `mappend` getSignature (pairs dgraph)) $ \dict -> do
  let convert :: forall v. Term (TermF id) v -> Term (TermF sid) v
      convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      convertBack :: Tree (TermN sid) Var -> Tree (TermN id) Var
      convertBack = mapTreeTerms (mapTermSymbols (fromJust . (`Map.lookup` dict')))
      dict' = Map.fromList $ fmap swap $ Map.toList dict
      trs' = fmap convert (getR p)
      dps' = fmap convert (getP p)
      typ' = InitialGoal (map (bimap convert convert) goals)
                         (Just $ mapDGraph convert dgraph)
                         (getFramework baseProblem)
      p'   = mkDPProblem typ' trs' dps'

  let (omegaConstraint, extraConstraintsAdded) = omega p'
  assertAll [castCircuit omegaConstraint]
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
                    ,fmap convertBack ec)
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
         ,TermF sid~ Family.TermF repr
         ,Ord tv, Observable tv
         ,Ord id, Show id, Pretty id
         ,FrameworkId sid
         ,MkDPProblem typ (NTRS sid)
         ,HasStatus sid
         ,HasFiltering sid
         ,HasPrecedence sid
         ,HasSignature (Problem typ trs)
         ,TermExtCircuit repr sid, CoTerm repr (TermF sid) tv v
         ,UsableSymbol sid
         ,MkDPProblem typ trs'
         ,Decode v Bool
         ,MonadSAT repr v m
         ,v ~ Var) =>
            Bool
         -> MkSATSymbol sid
         -> (problem' -> repr v)
         -> problem
         -> m (EvalM v ( ([Int], [Int]), BIEnv v, [sid]))
rpoAF_NDP allowCol mkS omega p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF allowCol mkS (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = fmap convert (getR p)
      dps' = fmap convert (getP p)
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


runRPOAF :: ( Co repr (Family.Var sid)
            , MonadSAT repr (Family.Var sid) m
            , Decode (Family.Var sid) Bool
            , HasFiltering sid
            , MonadReader env reader
            , Show id
            , Ord id
            , id ~ Family.Id sid
            ) => Bool
              -> MkSATSymbol sid
              -> Signature id
              -> (Map.Map id sid -> m (reader t))
              -> m (reader (t, env, [sid]))
runRPOAF allowCol i sig f = do
  let ids  = arities sig
     -- bits = calcBitWidth $ Map.size ids

  (symbols, constraints) <- unzip <$> mapM (mkSatSymbol i)  (Map.toList ids)

  forM_ (concat constraints) $ \(name, c) -> assert_ name [c]

  if allowCol
        -- do we need the then clause? surely mkSATSymbol is already demanding this?
    then assertAll [not(listAF s) --> one [inAF i s | i <- [1..a]]
                    | (s,a) <- zip symbols (Map.elems ids)]
    else assertAll (map listAF symbols)

  let dict       = Map.fromList (zip (Map.keys ids) symbols)
  mkRes <- f dict
  return $ do
    env <- ask
    res <- mkRes
    return (res, env, symbols)

-- ----------------------
-- Symbols set extensions
-- ----------------------

instance (Eq a, TermCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr) =>
    TermExtCircuit repr (Usable (RPOSsymbol v a)) where
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

instance (TermCircuit repr, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Ord a, Pretty a) =>
  TermExtCircuit repr (Usable(LPOSsymbol v a)) where
  exEq s t = lexpeq s t
  exGt s t = lexpgt s t
--  exGe = lexpge_exist

instance (TermCircuit repr, AssertCircuit repr, OneCircuit repr, ECircuit repr, ExistCircuit repr
         ,Pretty a, Ord a) =>
  TermExtCircuit repr (Usable(LPOsymbol v a)) where
  exEq s t = lexeq s t
  exGt s t = lexgt s t

instance (TermCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Pretty a, Ord a) =>
  TermExtCircuit repr (Usable(MPOsymbol v a)) where
  exEq s t = muleq s t
  exGt s t = mulgt s t

instance (TermCircuit repr, AssertCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         ,Pretty a, Ord a) =>
  TermExtCircuit repr (Usable(RPOsymbol v a)) where
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
    dd = getDefinedSymbols $ getR (iUsableRules p)
    go (Pure x) _ = and $ map iusable $ toList $ getDefinedSymbols (iUsableRulesVar p [] x)

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
       | otherwise                       = getDefinedSymbols $ getR (iUsableRules p)
    go (Pure x) _
       | getMinimalityFromProblem p == M = true
       | otherwise                       = and $ map iusable $ toList $ getDefinedSymbols (iUsableRulesVar p [] x)

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
    ip = involvedPairs p
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

omegaIGgen :: forall problem initialgoal id base.
              (problem ~ NProblem initialgoal id
              ,initialgoal ~ InitialGoal (TermF id) base
              ,Var ~ Family.Var id
              ,RPOProblemN initialgoal id
              ,RPOProblemN base id
              ,GenSymbol id
              ,Eq base
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
--   extraConstraints :: forall repr. (TermExtCircuit repr id, CoTerm repr (TermF id) Var) => [repr Var]
   extraConstraints = [ genTerm > term f (replicate i genTerm) | (f,i) <- Map.toList partial]
   partial = definedSymbols (getSignature p)
             `Map.difference`
             Map.fromList
             [(f, arity ) | l :-> r <- rules (getR p)
                          , Just f <- [rootSymbol l]
                          , isLinear l && P.all isVar (properSubterms l)
                          , let arity = length (properSubterms l)]

rulesFor :: (HasId1 t, Family.Id t ~ id, Eq id) => id -> [Rule t v] -> [Rule t v]
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
               , FrameworkProblem typ trs
               , HasSignature (Problem typ trs)
               , RPOId id
               ) =>
               Problem typ trs -> [Int] -> EvalM var (VerifyRPOAF rule)
verifyRPOAF p nonDecPairsIx = do
  let the_pairs = getP p
      the_rules = getR p
      npairs    = length $ rules the_pairs
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
                      rules$ getR (iUsableRules' p [] (rhs <$> theFilteredPairs))
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
  signature = getSignature p
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
