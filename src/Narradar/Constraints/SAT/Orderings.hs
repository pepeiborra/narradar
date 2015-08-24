{-# LANGUAGE TupleSections #-}
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

module Narradar.Constraints.SAT.Orderings (
   setupAF, reductionPair, reductionPairIG, reductionPairN, ruleRemoval
  ,runR, runRP
  ,omegaUsable, omegaNeeded
  ,omegaUsable', omegaNeeded'
  ,omegaIG, omegaIGgen, omegaNone
  ,convertTyp,convertTyp1,convertTypIG
  ,Usable, UsableSymbol(..), usableSymbol
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Data.Bifunctor
import Data.Functor1
import Data.Foldable (toList)
import Data.List ((\\), find, inits)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Funsat.TermCircuit (Co, CoTerm)
import Funsat.TermCircuit.Ext
import Narradar.Framework.Ppr as Ppr
import Narradar.Constraints.Syntactic
import Narradar.Constraints.SAT.MonadSAT
import Narradar.Constraints.SAT.Usable
import Narradar.Framework
import Narradar.Types.Term
import Narradar.Types.TRS
import Narradar.Types.Problem
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.NarrowingGen
import qualified Narradar.Types as Narradar
import Narradar.Utils hiding (none)

import qualified Data.Term.Family as Family
import qualified Prelude as P
import Prelude hiding (lex, not, and, or, any, all, quot, (>))

import Debug.Hoed.Observe

setupAF allowCol p = do
  unless allowCol $ assertAll (map listAF $ toList $ getAllSymbols p)
  return p

rewriteOrder p = do
  let trs = rules $ getR p
  decreasing_rules <- replicateM (length $  trs) boolean

  () <- pprTrace (text "asserting weak decreasingness of rules") $ return ()
  assertAll [ l >~ r | l:->r <- trs]

  () <- pprTrace (text "asserting strong decreasingness of rules") $ return ()
  assertAll [(l > r) <--> input dec | (l:->r, dec) <- trs `zip` decreasing_rules]

  () <- pprTrace (text "at least one rule is strongly dec. ") $ return ()
  assert (map input decreasing_rules)

  return $ do
    decreasing <- decode decreasing_rules
    let the_non_decreasing_rules = [ r | (r,False) <- zip [(0::Int)..] decreasing]
    return (the_non_decreasing_rules,[])

reductionPair omega p' = do
  let dps' = getP p'
  decreasing_dps <- replicateM (length $ rules dps') boolean

  () <- pprTrace (text "Asserting omega") $ return ()
  assertAll [omega p']

  () <- pprTrace (text "asserting weak decreasingness of pairs") $ return ()
  assertAll [ l >~ r | l:->r <- rules dps']

  () <- pprTrace (text "asserting strong decreasingness of pairs") $ return ()
  assertAll [(l > r) <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  () <- pprTrace (text "asserting that at least one pair is decreassing") $ return ()
  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  () <- pprTrace (text "assert that we find the best solution possible") $ return ()
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  () <- pprTrace (text "assert that only usable rules are selected") $ return ()
  mapM_ (assertW 1 . (:[]) . not . input . usable) (toList $ getAllSymbols p')

  return $ do
    decreasing <- decode decreasing_dps
    let the_non_decreasing_pairs = [ r | (r,False) <- zip [(0::Int)..] decreasing]
    return (the_non_decreasing_pairs,[])


ruleRemoval p' = do
  let trs  = getR p'
  let dps' = getP p'
  decreasing_rules <- replicateM (length $ rules dps') boolean

  () <- pprTrace (text "Asserting weak decreasingness of rules") $ return ()
  assertAll [ l >~ r | l:->r <- rules trs]

  () <- pprTrace (text "asserting weak decreasingness of pairs") $ return ()
  assertAll [ l >~ r | l:->r <- rules dps']

  () <- pprTrace (text "asserting strong decreasingness of rules") $ return ()
  assertAll [(l > r) <--> input dec | (l:->r, dec) <- rules trs `zip` decreasing_rules]

  () <- pprTrace (text "asserting that at least one rule is decreassing") $ return ()
  assert (map input decreasing_rules)

  -- Ensure that we find the solution which removes the most pairs possible
  () <- pprTrace (text "assert that we find the best solution possible") $ return ()
  sequence_ [ assertW 1 [input b] | b <- decreasing_rules]

  return $ do
    decreasing <- decode decreasing_rules
    let the_non_decreasing_rules = [ r | (r,False) <- zip [(0::Int)..] decreasing]
    return (the_non_decreasing_rules,[])


reductionPairIG :: ( UsableSymbol id
                   , IsDPProblem typ
                   , HasSignature (Problem typ (NTRS id))
                   , FrameworkId id
                   , MonadSAT repr Var m
                   , TermCircuit repr
                   , Family.TermF repr ~ TermF id
                   , Family.Var   id   ~ Var
                   , CoTerm repr (TermF id) Narradar.Var Var
                   ) => (Problem typ (NTRS id)
                         -> ( Tree (TermN id) Var
                            , EvalM Var t))
                   -> Problem typ (NTRS id)
                   -> m (EvalM Var ([Int], t))
reductionPairIG omega p' = do
  let dps' = getP p'
  let (omegaConstraint, extraConstraintsAdded) = omega p'
  assertAll [castCircuit omegaConstraint]
  assertAll [ l >~ r | l:->r <- rules dps']

  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [input b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  mapM_ (assertW 1 . (:[]) . not . input . usable) (toList $ getAllSymbols p')

--  debug ("\nThe indexes are: " ++ show decreasing_dps) $
  return $ do
             decreasing <- decode decreasing_dps
             ec <- extraConstraintsAdded
             return ([ r | (r,False) <- zip [(0::Int)..] decreasing]
                    , ec)
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

reductionPairN ::
  (CoTerm repr (TermF id) Narradar.Var Var
  ,MonadSAT repr Var m
  ,Family.TermF repr ~ TermF id
  ,Family.Var   id   ~ Var
  ,FrameworkId id, UsableSymbol id
  ,HasFiltering id
  ,TermCircuit repr
  ,IsDPProblem typ
  ,HasSignature (NProblem typ id)
  ) => (NProblem typ id -> repr Var) -> NProblem typ id -> m (EvalM Var (([Int], [Int]), [t]))
reductionPairN omega p' = do
  let (dps') = getP p'
  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  let af_ground_rhs_dps :: forall repr. (Circuit repr, Co repr Var) => [repr Var]
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
  mapM_ (assertW 1 . (:[]) . not . input . usable) (toList $ getAllSymbols p')

  return $ do
    decreasing <- decode decreasing_dps
    af_ground  <- decode (af_ground_rhs_dps :: [Eval Var])
    return (([ r | (r,False) <- zip [(0::Int)..] decreasing]
            ,[ r | (r,False) <- zip [(0::Int)..] af_ground])
           ,[])

initialize i sig f = do
  let ids  = arities sig
     -- bits = calcBitWidth $ Map.size ids

  (symbols, constraints) <- unzip `liftM` mapM (mkSatSymbol i) (Map.toList ids)

  forM_ (concat constraints) $ \(name, c) -> assert_ name [c]

  let dict       = Map.fromList (zip (Map.keys ids) symbols)
  mkRes <- f dict
  return $ do
    env <- ask
    res <- mkRes
    return (res, env, symbols)


runRP (O o oo) mkS mkTyp p rp
  = initialize mkS (getSignature p) $ \dict -> do
  let convert = mapTermSymbols fId
      fId f = fromJust $ Map.lookup f dict
      convertBack = mapTreeTerms (mapTermSymbols (fromJust . (`Map.lookup` dict')))
      dict' = Map.fromList $ fmap swap $ Map.toList dict
      trs' = fmap convert (getR p)
      dps' = fmap convert (getP p)
      typ' = mkTyp fId $ getFramework p
      p'   = mkDPProblem typ' trs' dps'
  resEvalM <- rp p'
  return $ do
    (dec, extraConstraints) <- resEvalM
    return (dec, convertBack <$> extraConstraints)

runR (O o oo) mkS mkTyp p rp
  = initialize mkS (getSignature p) $ \dict -> do
  let convert = mapTermSymbols fId
      fId f = fromJust $ Map.lookup f dict
      convertBack = mapTreeTerms (mapTermSymbols (fromJust . (`Map.lookup` dict')))
      dict' = Map.fromList $ fmap swap $ Map.toList dict
      trs' = fmap convert (getR p)
      typ' = mkTyp fId $ getFramework p
      p'   = mkProblem typ' trs'
  resEvalM <- rp p'
  return $ do
    (dec, extraConstraints) <- resEvalM
    return (dec, convertBack <$> extraConstraints)

-- -------------------------
-- Convering problem types
-- -------------------------

convertTyp  _ = id
convertTyp1 fId = fmap1 (bimap fId id)

convertTypIG :: forall id sid base.
                (Observable sid, Ord sid, Ord id) =>
                (id -> sid)
                -> InitialGoal (TermF  id) base
                -> InitialGoal (TermF sid) base
convertTypIG fId (InitialGoal goals dgraph base) =
             InitialGoal (map (bimap convert convert) goals)
                         (mapDGraph convert <$> dgraph)
                         base
  where
    convert :: forall v. Term (TermF id) v -> Term (TermF sid) v
    convert = mapTermSymbols fId

-- ------------------------
-- Usable Rules with AF
-- ------------------------
omegaNone p =  and ([ l >~ r | l:->r <- rules (getR p)] ++
                    [ iusable f | f <- Set.toList $ getDefinedSymbols (getR p)])

omegaUsable = omegaUsable' inAF
omegaUsable' inAF p = -- pprTrace ("Solving P=" <> getP p $$ "where dd = " <> dd) $
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

omegaNeeded = omegaNeeded' inAF
omegaNeeded' inAF p = pprTrace (text "Solving P=" <+> getP p $$ text "where dd = " <+> dd) $
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

omegaIG :: (TermCircuit repr, ECircuit repr
           ,CoTerm repr (TermF id) Narradar.Var Var
           ,FrameworkId id, UsableSymbol id, HasFiltering id
           ,FrameworkProblem (InitialGoal (TermF id) base) (NTRS id)
           ,FrameworkProblem base (NTRS id)
           ,Family.TermF repr ~ TermF id
           ,Family.Var   id   ~ Var
           ) =>
           Problem (InitialGoal (TermF id) base) (NTRS id)
           -> repr Var
omegaIG p = --pprTrace ("Solving P=" <> getP p $$ "where the involved pairs are: " <> ip $$ text "and dd=" <+> dd ) $
           (and ([go l r trs | l:->r <- ip] ++
                 [iusable f --> and [ l >~ r | l:->r <- rulesFor f trs]
                    | f <- Set.toList dd ] ++
                 [not(iusable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                )
           )

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
              ,FrameworkProblemN initialgoal id
              ,FrameworkProblemN base id
              ,GenSymbol id, UsableSymbol id, Ord id, HasFiltering id
              ,Family.Var id ~ Var
              ,Eq base
              ) => problem -> (Tree (TermN id) Var, EvalM Var [Tree (TermN id) Var])
omegaIGgen p
  | isLeftLinear (getR p) = pprTrace ("omegaIGgen: partial = " <+> partial)
                            (omegaIG p, return [])
  | omegaConstraint <- omegaIG p
  = (omegaConstraint /\ (iusable gen --> and extraConstraints)
    ,do { b  <- decode (isEval $ iusable gen);
          return $
           if b then extraConstraints
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
