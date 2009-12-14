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

module Narradar.Constraints.SAT.RPOAF (
   RPOSsymbol(..), SymbolRes(..), RPOsymbol(..), LPOsymbol(..), LPOSsymbol(..), MPOsymbol(..)
  ,rpoAF_DP, rpoAF_NDP, rpoAF_IGDP, Omega
  ,rpo, rpos, lpo, lpos, mpo
  ,verifyRPOAF
  ) where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Identity
import Control.Monad.List
import qualified Control.RMonad as R
import qualified Data.Array as A
import Data.Foldable (Foldable, foldMap, toList)
import Data.List ((\\), transpose, inits, zip4)
import Data.Maybe
import Data.Monoid
import Data.NarradarTrie (HasTrie)
import Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Narradar.Framework.Ppr as Ppr

import Narradar.Constraints.SAT.Combinators
import Narradar.Constraints.SAT.RPOAF.Symbols
import qualified Narradar.Constraints.RPO as RPO
import qualified Narradar.Types as Narradar
import Narradar.Types hiding (symbol, fresh, constant, Var)
import Narradar.Types.Problem.InitialGoal
import Narradar.Utils
import Narradar.Types.ArgumentFiltering (AFId)

import qualified Funsat.ECircuit as ECircuit
import qualified Narradar.Types.ArgumentFiltering as AF
import qualified Prelude as P
import Prelude hiding (catch, lex, not, and, or, any, all, quot, (>))

-- | RPO + AF

rpoAF rpo allowCol trs = runRPOAF rpo allowCol (getSignature trs) $ \dict -> do
  let symb_rules = mapTermSymbols (\f -> fromJust $ Map.lookup f dict) <$$> rules trs
  let problem = and [ l > r | l:->r <- symb_rules]
  assert [problem]
  return (return ())


-- | RPO + AF + Usable Rules
rpoAF_DP col ex p = rpoAF_DP' col ex p
rposAF_P col p = rpoAF_DP' col rpos p
lposAF_DP col p = rpoAF_DP' col lpos p
lpoAF_DP col p = rpoAF_DP' col (lpo) p
mpoAF_DP col p = rpoAF_DP' col (mpo) p


-- | Returns the indexes of non decreasing pairs and the symbols used
rpoAF_DP' allowCol con p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF con allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs'    = mapNarradarTRS convert (getR p)
      dps'    = mapNarradarTRS convert (getP p)
      p'      = mkDPProblem (getProblemType p) trs' dps'

  decreasing_dps <- replicateM (length $ rules dps') boolean

--  assertAll [omega p']
  assertAll [ l >~ r | l:->r <- rules dps']

  assertAll [(l > r) <-->  input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]
  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [lit b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected
  mapM_ (assertW 1 . (:[]) . negate . lit . usable) (Map.elems dict)

  return $ do
    decreasing <- decode decreasing_dps
    let the_non_decreasing_pairs = [ r | (r,False) <- zip [0..] decreasing]
    return the_non_decreasing_pairs


rpoAF_IGDP :: (Ord id
              ,Traversable (Problem base), Pretty base
              ,MkDPProblem base (NTRS sid)
              ,NUsableRules base sid
              ,NCap base sid
              ,NeededRules (TermF sid) Narradar.Var base (NTRS sid)
              ,HasMinimality base
              ,DPSymbol id, Pretty id
              ,RPOExtCircuit (Shared sid) sid
              ,Ord sid, Pretty sid, Show sid
              ,UsableSymbol Var sid
              ,DPSymbol sid
              ,HasPrecedence Var sid
              ,HasStatus Var sid
              ,HasFiltering Var sid
              ,HasTrie sid
              ,Decode sid (SymbolRes id) Var
              ) => Bool -> (Int -> (id,Int,Bool) -> SAT sid Var sid)
                -> NProblem (InitialGoal (TermF id) base) id
                -> SAT sid Var (EvalM Var ([Int], [SymbolRes id]))

rpoAF_IGDP allowCol con p@InitialGoalProblem{..}
  = runRPOAF con allowCol (getSignature p `mappend` getSignature (pairs dgraph)) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      typ' = InitialGoal (map convert goals)
                         (Just $ mapDGraph convert dgraph)
                         (getProblemType baseProblem)
      p'   = mkDPProblem typ' trs' dps'

  assertAll (omega  p' : [ l >~ r | l:->r <- rules dps'])

  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  assert (map input decreasing_dps)

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [lit b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected


--  debug ("\nThe indexes are: " ++ show decreasing_dps) $
  return $ do

    decreasing <- decode decreasing_dps

    (weakly, strictly) <- do
       weakly   <- evalB (and $ omega  p' :
                               [l >~ r | (False, l:->r) <- zip decreasing (rules dps')])
       strictly <- evalB (and [l > r | (True, l:->r) <- zip decreasing (rules dps')])
       return (weakly, strictly)
    (weaklyS, strictlyS) <- do
       weaklyS <- evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $
                        and $ omega p' : [l >~ r | (False, l:->r) <- zip decreasing (rules dps')])

       strictlyS <- evalB (ECircuit.removeComplex $ ECircuit.runShared $ removeComplex $ runShared $
                           and [l > r | (True, l:->r) <- zip decreasing (rules dps')])

       return (weaklyS, strictlyS)
{-
    verification <- verifyRPOAF (getProblemType p) trs' dps' decreasing_dps
    let isValidProof
          | isCorrect verification = True
          | otherwise = pprTrace verification False

    CE.assert isValidProof $
-}

    CE.assert strictlyS $
     CE.assert weaklyS $
     CE.assert strictly $
--     CE.assert weakly $
     return [ r | (r,False) <- zip [0..] decreasing]

 where isTheRightKind :: InitialGoal (f id) base -> InitialGoal (f id) base
       isTheRightKind = id

rpoAF_NDP allowCol con p
  | _ <- isNarradarTRS1 (getR p)
  = runRPOAF con allowCol (getSignature p) $ \dict -> do
  let convert = mapTermSymbols (\f -> fromJust $ Map.lookup f dict)
      trs' = mapNarradarTRS convert (getR p)
      dps' = mapNarradarTRS convert (getP p)
      p'   = mkDPProblem (getProblemType p) trs' dps'

  decreasing_dps <- replicateM (length $ rules dps') boolean
  assertAll [l > r <--> input dec | (l:->r, dec) <- rules dps' `zip` decreasing_dps]

  let af_ground_rhs_dps = map afGroundRHS (rules dps')

  assert (map input decreasing_dps)
  assert af_ground_rhs_dps
  assertAll (omega  p' :
             [ l >~ r | l:->r <- rules dps'])

  -- Ensure that we find the solution which removes the most pairs possible
  sequence_ [ assertW 1 [lit b] | b <- decreasing_dps]

  -- Ensure that only really usable rules are selected


  return $ do
    decreasing <- decode decreasing_dps
    af_ground  <- decode (af_ground_rhs_dps :: [Eval Var])
    return ([ r | (r,False) <- zip [0..] decreasing]
           ,[ r | (r,False) <- zip [0..] af_ground])


runRPOAF con allowCol sig f = do
  let ids  = getArities sig
      bits = calcBitWidth $ Map.size ids

  symbols <- mapM (con bits)
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
    symbolsres <- mapM decode symbols
    res <- mkRes
    return (res, symbolsres)

-- ----------------------
-- Symbols set extensions
-- ----------------------

instance (RPOCircuit repr (RPOSsymbol v a), FreshCircuit repr, OneCircuit repr, ECircuit repr, Ord a) =>
    RPOExtCircuit repr (RPOSsymbol v a) where
     exEq s t ss tt =
       and [useMul s, useMul t, muleq s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpeq s t ss tt]

     exGt s t ss tt =
       and [useMul s, useMul t, mulgt s t ss tt]
       \/
       and [not$ useMul s, not$ useMul t, lexpgt s t ss tt]

instance (RPOCircuit repr (LPOSsymbol v a), OneCircuit repr, ECircuit repr, Ord a) =>
  RPOExtCircuit repr (LPOSsymbol v a) where
  exEq s t = lexpeq  s t
  exGt s t = lexpgt  s t

instance (RPOCircuit repr (LPOsymbol v a), OneCircuit repr, ECircuit repr, Ord a) =>
  RPOExtCircuit repr (LPOsymbol v a) where
  exEq s t = lexeq s t
  exGt s t = lexgt s t

instance (RPOCircuit repr (MPOsymbol v a), FreshCircuit repr, OneCircuit repr, ECircuit repr, Ord a) =>
  RPOExtCircuit repr (MPOsymbol v a) where
  exEq s t = muleq s t
  exGt s t = mulgt s t

instance (RPOCircuit repr (RPOsymbol v a), FreshCircuit repr, OneCircuit repr, ECircuit repr, Ord a) =>
  RPOExtCircuit repr (RPOsymbol v a) where
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

-- -----------------------------------
-- Lexicographic extension with AF
-- -----------------------------------

lexgt id_f id_g ff gg = go (zip ff [1..]) (zip gg [1..]) where
  go []     []     = false
  go []     _      = false
  go ff      []    = or [inAF i id_f | (_,i) <- ff]
  go ((f,i):ff) ((g,j):gg)
    =  ite (inAF i id_f)
           (ite (inAF j id_g)
                ((f > g) \/ ((f ~~ g) /\ go ff gg))
                (go ((f,i):ff) gg))
           (go ff ((g,j):gg))

lexeq id_f id_g ff gg = go (zip ff [1..]) (zip gg [1..]) where
  go []         [] = true
  go ff         [] = not $ or [inAF i id_f | (_,i) <- ff]
  go []         gg = not $ or [inAF j id_g | (_,j) <- gg]
  go ((f,i):ff) ((g,j):gg)
    = ite (inAF i id_f)
          (ite (inAF j id_g)
               ((f ~~ g) /\ go ff gg)
               (go ((f,i):ff) gg))
          (go ff ((g,j):gg))

--lexpeq :: (ECircuit repr, RPOCircuit repr (Symbol a)) =>
--          Symbol a -> Symbol a -> [TermN (Symbol a)] -> [TermN (Symbol a)] -> repr Var
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

lexpgt id_f id_g ss tt = exgt_k (transpose $ enc_f) (transpose $ enc_g)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g
       n = length ss
       m = length tt
       exgt_k [] _ = false
       exgt_k (f_k:_) [] = or f_k
       exgt_k (f_k:ff) (g_k:gg)
         = or [f_ik /\ and [ g_jk --> s_i > t_j \/
                                      (s_i ~~ t_j /\ exgt_k ff gg)
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_i,f_ik, s_i) <- zip3 enc_f f_k ss]

-- ---------------------------
-- Multiset extension with AF
-- ---------------------------

-- We avoid memoizing constraints derived from multiset extensions,
-- There is nothing to win since the involved gammas and epsilons are fresh for
-- every multiset comparison and do not carry over to the rest of the problem

mulgt id_f id_g [] _  = false
--mulgt id_f id_g [x] [y] = inAF 1 id_f /\ (inAF 1 id_g --> x > y)
mulgt id_f id_g ff gg =
    mulgen id_f id_g ff gg (\epsilons ->
                                not $ and [inAF i id_f --> ep_i
                                           | (i, ep_i) <- zip [1..] epsilons])
muleq id_f id_g [] [] = true
--muleq id_f id_g [t] [u] = (not(inAF 1 id_f) /\ not (inAF 1 id_g)) \/ (inAF 1 id_f /\ inAF 1 id_g /\ t ~~ u)
muleq id_f id_g ff gg =
    mulgen id_f id_g ff gg (\epsilons ->
                                and [inAF i id_f --> ep_i
                                      | (i, ep_i) <- zip [1..] epsilons])

mulgen id_f id_g ff gg k = (`runCont` id) $ do
    let (i,j)    = (length ff, length gg)

    epsilons <-  replicateM i (Cont fresh)
    gammasM  <-  replicateM j $ replicateM i (Cont fresh)
    let gammasM_t = transpose gammasM

        oneCoverForNonFilteredSubtermAndNoCoverForFilteredSubterms =
          [ ite (inAF j id_g)
                (one gammas_j)
                (and (not <$> gammas_j))
            | (j, gammas_j) <- zip [1..] gammasM ]

        filteredSubtermsCannotCover =
          [ not(inAF i id_f) --> and (not <$> gammas_i)
            | (i, gammas_i) <- zip [1..] gammasM_t]

        subtermUsedForEqualityCanOnlyCoverOnce =
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
          ++ subtermUsedForEqualityCanOnlyCoverOnce
          ++ greaterOrEqualMultisetExtension
           )

-- ------------------------
-- Usable Rules with AF
-- ------------------------
class Omega typ id where
    omega :: (ECircuit repr, RPOCircuit repr id) => Problem typ (NTRS id) -> repr Var

instance (p  ~ Problem typ
         ,IsDPProblem typ
         ,HasMinimality typ
         ,trs ~ NTRS id
         ,t   ~ TermF id
         ,v   ~ Narradar.Var
         ,Traversable p
         ,Ord id
         ,HasFiltering Var id, UsableSymbol Var id
         ,Pretty id
         ,NUsableRules typ id
         ,NeededRules t v typ trs
         ,MkDPProblem typ (NTRS id)
         ,RPOExtCircuit (Shared id) id
         ,HasPrecedence Var id
         ,HasStatus Var id
         ) => Omega typ id
 where
  omega p = and ([go r trs | _:->r <- dps] ++
                 [iusable f --> and [ l >~ r | l:->r <- rulesFor f trs]
                   | f <- Set.toList dd ] ++
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

instance (p   ~ Problem (InitialGoal (TermF id) typ)
--         ,id ~ SignatureId (Problem typ trs), id ~ symbol a
         ,t   ~ TermF id
         ,v   ~ Narradar.Var
         ,trs ~ NarradarTRS t v
         ,HasMinimality typ
         ,Pretty typ
         ,MkDPProblem typ trs
         ,HasSignature (Problem typ trs)
         ,Traversable (Problem typ)
         ,Pretty id, Ord id, DPSymbol id
         ,HasFiltering Var id, UsableSymbol Var id
         ,NUsableRules typ id
         ,NeededRules t v typ trs
         ,NCap typ id
         ,HasPrecedence Var id, HasStatus Var id
         ,RPOExtCircuit (Shared id) id
         ) => Omega (InitialGoal (TermF id) typ) id
 where

  omega p = --pprTrace ("Solving P=" <> getP p $$ "where the involved pairs are: " <> ip) $
            and ([go l r trs | l:->r <- ip] ++
                 [iusable f --> and [ l >~ r | l:->r <- rulesFor f trs]
                    | f <- Set.toList dd ] ++
                 [not(iusable f) | f <- Set.toList (getDefinedSymbols sig `Set.difference` dd)]
                )

   where
    ip = forDPProblem involvedPairs p
    (trs,dps) = (rules $ getR p, rules $ getP p)
    sig = getSignature (getR p)
    dd
       | getMinimalityFromProblem p == M = getDefinedSymbols $ getR (neededRules p (rhs <$> dps))
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
            :  [ go l r rest | l:->r <- rls ]
            ++ [ inAF i id_t --> go l t_i rest
                   | (i, t_i) <- zip [1..] tt ]
            )
       where
         Just id_t = rootSymbol t
         tt        = directSubterms t
         rls       = rulesFor id_t trs
         rest      = trs \\ rls -- :: [Rule t Var]

rulesFor :: (HasId t, TermId t ~ id, Eq id) => id -> [Rule t v] -> [Rule t v]
rulesFor f trs = [ l:->r | l:-> r <- trs, rootSymbol l == Just f ]

-- --------
-- Testing
-- --------

{-
verifyRPOAF :: (var ~ Var
               ,HasFiltering var symb
               ,HasStatus    var symb
               ,HasPrecedence var symb
               ,NUsableRules typ symb
          ) => typ -> NTRS symb -> NTRS symb -> [var]
           -> EvalM var (VerifyRPOAF (RuleN symb))
-}
verifyRPOAF typ the_rules the_pairs dec_pairs = do

  theAf <- AF.fromList' `liftM` mapM getFiltering (toList $ getAllSymbols signature)
  let theFilteredPairs = rules $ AF.apply theAf the_pairs

  decPairs <- mapM (evalDecode . input) dec_pairs

  let theDecPairs = CE.assert (P.all (P.< npairs) decPairs) $
                  select decPairs (rules the_pairs)
      theWeakPairs = select ([0..npairs - 1] \\ decPairs) (rules the_pairs)

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
    isListAF  <- evalDecode $ listAF s
    filterings <- mapM evalDecode [inAF i s | i <- [1..pred(getArity signature s)]]
    let positions = [ i | (i,True) <- zip [1..pred(getArity signature s)] filterings]
    return $ if isListAF
              then (s, Right positions)
              else CE.assert (length positions == 1) $
                   (s, Left $ head positions)

  npairs    = length (rules the_pairs)



