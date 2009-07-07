{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Narradar.Processor.PrologProblem where -- (inferType, prologP_sk, prologP_labelling_sk, skTransform) where

import Control.Applicative
import Control.Arrow (first, second, (***))
import Control.Exception (assert)
import Control.Monad.Identity (Identity(..))
import Control.Monad.Reader (MonadReader(..), Reader(..))
import Control.Monad.State
import Control.Monad.Writer (MonadWriter(..), Writer(..), WriterT(..), Any(..))
import Control.Monad.Supply
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.AlaCarte as Al
import Data.AlaCarte.Ppr
import Data.Char (isSpace)
import Data.List hiding (any,notElem)
import Data.Maybe
import Data.Monoid      (Monoid(..))
import Data.Foldable    (Foldable(foldMap), toList, notElem)
import Data.Traversable (Traversable)
import qualified Data.Foldable    as F
import qualified Data.Traversable as T
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Haskell.TH (runIO)
import Text.ParserCombinators.Parsec (parse)
import Text.PrettyPrint as Ppr hiding (Mode(..))
import System.IO.Unsafe

import Data.Term.Rules
import Data.Term.Var as Prolog (Var(VName, VAuto))
import Language.Prolog.Syntax (Program, Program'', Clause, ClauseF(..), GoalF(..), mapPredId,
                               TermF(Cons, Nil, Tuple, Wildcard, String, Int, Float))
import qualified Language.Prolog.Syntax as Prolog
import qualified Language.Prolog.Parser as Prolog (program)
import Language.Prolog.Signature
import Language.Prolog.SharingAnalysis (infer)
import Language.Prolog.PreInterpretation (computeSuccessPatterns, ComputeSuccessPatternsOpts(..),
                                          computeSuccessPatternsOpts, DatalogTerm, Abstract,
                                          abstractCompileGoal)
import qualified Language.Prolog.Representation as Prolog
import Language.Prolog.Representation (representTerm, representProgram,
                                       Term0, term0, T(..), PrologT, PrologP, V, NotVar, Compound(..),
                                       cons, nil, psucc, zero, tup, eq, is,
                                       NotAny, PrologTerm, any, notvar, compound, mkT,
                                       isNotvar, isAny)
import Language.Prolog.Transformations (QueryAnswer(..))

import TRSTypes (Mode(..))
import Narradar.Framework.Proof
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.ArgumentFiltering (AF_, MkHeu, mkHeu, PolyHeuristicN, Heuristic(..), simpleHeu, innermost)
import Narradar.Types hiding (Var,Term, program)
import Narradar.Types as Narradar
import Narradar.Utils
import Prelude hiding (and,or,any,notElem,pi)
import qualified Prelude

type PF   = PrologT :+: PrologP :+: T String
type P    = Expr PF
type RP   = PrologId P
type LP   = Labelled P
type DRP  = Identifier RP
type LRP  = Labelled RP
type DLRP = Identifier LRP

instance Convert RP   DLRP where convert = IdFunction . Plain
instance Convert DRP  DLRP where convert = fmap Plain
instance Convert LRP  DRP  where convert = IdFunction . unlabel
instance Convert RP   RP   where convert = id
instance Convert DRP  DRP  where convert = id
instance Convert LRP  LRP  where convert = id
instance Convert DLRP DLRP where convert = id

-- ---------
-- Analysis
-- ---------
inferType (Problem Prolog{program} _ _) = infer program


-- --------------
-- Processors
-- --------------

prologP_sk :: (PolyHeuristicN heu DRP, MonadPlus m, MonadFree ProofF m) =>
              MkHeu heu -> PrologProblem Narradar.Var -> m (Problem DRP Narradar.Var)
prologP_sk heu p0@(Problem Prolog{..} _ _) =
   andP PrologSKP p0
     [ msum (map return pp)
         | let sk_p          = prologTRS' $ skTransform (prepareProgram $ addMissingPredicates program)
         , goal0            <- goals
         , let goal          = skTransformAF program goal0
               af_groundinfo = AF.init sk_p `mappend` goal
               pp            = mkGoalProblem heu GNarrowingModes{goal, pi=af_groundinfo} sk_p
     ]

prologP_labelling_sk :: (PolyHeuristicN heu LRP, PolyHeuristicN heu DLRP, MonadFree ProofF m, v ~ Narradar.Var) =>
                        MkHeu heu -> PrologProblem v -> m (Problem DLRP v)
prologP_labelling_sk mkHeu p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingSKP [] :: ProcInfo LRP) p0
  | otherwise  = mall problems
  where problems = do
                       goal <-goals
                       let goal_lps = AF.mapSymbols' (flip Labelling) (skTransformAF program goal)
                       (prolog_rr, pi, sig) <- toList $ labellingPredsTrans mkHeu goal program
                       let trs   = PrologTRS prolog_rr sig
                           pp'   = mkGoalProblem mkHeu GNarrowingModes{pi, goal = goal_lps} trs
                           modes = Map.keys prolog_rr
                       return $ orP (LabellingSKP modes) p0 (map return pp')


prologP_labelling_cons :: (MonadFree ProofF m, v ~ Narradar.Var) =>
                        [FilePath] -> PrologProblem v -> m (Problem DLRP v)
prologP_labelling_cons paths p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingCP [] :: ProcInfo LRP) p0
  | otherwise  = mall problems
  where problems = do
                       g      <- goals
                       (f,ii) <- AF.toList g
                       let query = (f, [ if i `elem` ii then G else V | i <- [1..getArity program f]])
                           goal  = AF.mapSymbols Plain (skTransformAF program g)
                       ((trs, pi), modes) <- toList $ labellingConsTrans paths query program
                       let pp'     = mkGoalProblem (simpleHeu innermost) GNarrowingModes{pi, goal} (prologTRS' trs)
                           newCons = Set.toList modes
                       return $ orP (LabellingCP newCons) p0 (map return pp')

prologP_labelling_all :: (MonadFree ProofF m, v ~ Narradar.Var) =>
                        [FilePath] -> PrologProblem v -> m (Problem DLRP v)
prologP_labelling_all paths p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingCP [] :: ProcInfo LRP) p0
  | otherwise  = mall problems
  where problems = do
                       g      <- goals
                       (f,ii) <- AF.toList g
                       let query = (f, [ if i `elem` ii then G else V | i <- [1..getArity program f]])
                           goal  = AF.mapSymbols Plain (skTransformAF program g)
                       ((trs, pi), modes) <- Set.toList $ labellingConsAndPredsTrans paths query program
                       let pp'     = mkGoalProblem (simpleHeu innermost) GNarrowingModes{pi, goal} (prologTRS' trs)
                           newCons = Set.toList modes
                       return $ orP (LabellingCP newCons) p0 (map return pp')

-- ----------------
-- Transformations
-- ----------------

type PrologRules id v = Map (WithoutPrologId id) (Set (RuleN id v))

skTransform :: (Ord id, Ord v, Ppr id) =>
                [Prolog.Clause'' id (TermN id v)] -> PrologRules (PrologId id) v
skTransform = runSk . skTransformWithM (\(Pred id _ :- _) -> id)

skTransformWith  mkIndex = runSk . skTransformWithM mkIndex
skTransformWithM mkIndex clauses = do
  clauseRules <- mapM (runClause . toRule) clauses
  return (Map.fromListWith mappend clauseRules)
 where   -- The counter for u_i is global,
         -- the list of vars is local to each clause.
       runClause = (`evalStateT` mempty)

       toRule c@(Pred id tt :- (filter (/= Cut) -> [])) = do
         let tt' = mapTermSymbols FunctorId <$> tt
         return (mkIndex c, Set.singleton (term (InId id) tt' :-> term (OutId id) tt'))

       toRule c@(Pred id tt :- (filter (/= Cut) -> gg)) = do
         let tt' = mapTermSymbols FunctorId <$>  tt
             gg' = mapTermSymbols FunctorId <$$> gg
         modify (getVars tt' `mappend`)
         rhs_0  <- mkRhs (head gg')
         mid_r  <- forM (gg' `zip` tail gg') $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg')
         let r_0 = term (InId id) tt' :-> rhs_0
             r_n = lhs_n :-> term (OutId id) tt'
         return (mkIndex c, Set.fromList (r_0 : r_n : mid_r))

       mkRhs (Pred id tt) = mkRhs' id tt
       mkRhs' id tt = do
         vv  <- toList <$> get
         i   <- next
         return (term (UId i) (term (InId id) tt : map Pure vv))

       mkLhs (Pred id tt) = mkLhs' id tt
       mkLhs' id tt = do
         vv  <- toList <$> get
         modify(getVars tt `mappend`)
         i   <- current
         return (term (UId i) (term (OutId id) tt : map Pure vv))

runSk = runSupply


class (Ord id, Ord id') => SkTransformAF id id' | id -> id' where skTransformAF :: HasSignature sig id => sig -> AF_ id -> AF_ id'

instance (T String :<: f, Ord (Expr f)) => SkTransformAF String (PrologId (Expr f)) where
  skTransformAF sig = AF.mapSymbols (\f -> if f `Set.member` getDefinedSymbols sig
                                         then InId (mkT f)
                                         else FunctorId (mkT f))

instance (T String :<: f, Ord (Expr f)) => SkTransformAF (Labelled String) (Labelled (PrologId (Expr f))) where
  skTransformAF sig = AF.mapSymbols (\f@(Labelling l t) -> if f `Set.member` getDefinedSymbols sig
                                         then Labelling l (InId (mkT t))
                                         else Labelling l (FunctorId (mkT t)))

prepareProgram :: (f ~ (PrologT :+: PrologP :+: T id)) =>
                  Program id -> Program'' (Expr f) (TermN (Expr f) Narradar.Var)
prepareProgram = (`evalState` mempty) . (`evalStateT` (toEnum <$> [0..]))
                 . representProgram toVar term (Pure <$> freshVar)
    where
         toVar (VName id)  = do
           env <- lift get
           case Map.lookup id env of
             Nothing -> do Var _ i <- freshVar
                           let v' = Var (Just id) i
                           lift(put (Map.insert id v' env))
                           return2 v'
             Just v  -> return2 v

         toVar (VAuto  id) = return (Narradar.var id)


Right preludePl = $(do pgm <- runIO (readFile "prelude.pl")
                       case parse Prolog.program "prelude.pl" pgm of -- parse just for compile time checking
                         Left err  -> error (show err)
                         Right _ -> [| fromRight <$$> parse Prolog.program "prelude.pl" pgm |]
                   )                 -- actual parsing ^^ happens (again) at run time.
                                     -- I am too lazy to write the required LiftTH instances.

preludePreds = Set.fromList [ f | Pred f _ :- _ <- preludePl]

addMissingPredicates cc0
  | Set.null undefined_cc0 = (insertIs . insertEqual) cc0
  | otherwise              = (insertDummy . insertIs . insertEqual . insertPrelude) cc0

   where undefined_cc0 = undefinedPreds cc0

         undefinedPreds    cc = Set.fromList [ f | f <- toList (getDefinedSymbols cc `Set.difference` definedPredicates cc)]
         definedPredicates cc = Set.fromList [ f | Pred f _ :- _ <- cc]

         insertEqual       cc = if getAny $ foldMap2 (Any . isEqual) cc then eqclause `mappend` cc else cc
         insertIs          cc = if getAny $ foldMap2 (Any . isIs)    cc then isclause `mappend` cc else cc

         eqclause = let x = return (toEnum 1) in [x :=: x :- []]
         isclause = let x = return (toEnum 1) in [Is x x :- []]
         isEqual (_ :=: _) = True; isEqual _ = False
         isIs Is{} = True; isIs _ = False

         insertPrelude cc = if not (Set.null (Set.intersection (undefinedPreds cc) preludePreds)) then cc' `mappend` cc else cc
           where cc' = foldr renamePred (cc `mappend` preludePl) (toList repeatedIdentifiers)
                 repeatedIdentifiers = preludePreds `Set.intersection` definedPredicates cc0
         insertDummy cc =  [ Pred f (take (getArity cc f) vars) :- [] | f <- toList (undefinedPreds cc)] ++ cc
         renamePred f = fmap2 (rename (findFreeSymbol cc0 f))
           where rename f' (Pred f tt) | f == f' = Pred f' tt
                 rename _ x = x

         vars = [Prolog.var ("X" ++ show i) | i <- [0..]]


findFreeSymbol sig pre = fromJust $ find (`Set.notMember` getAllSymbols sig) (pre : [pre ++ show i | i <- [0..]])


labellingPredsTrans :: forall heu v.
                       (PolyHeuristicN heu LRP, v ~ Narradar.Var) =>
                          MkHeu heu -> AF_ String -> Prolog.Program String
                       -> Set(PrologRules LRP v, AF_ LRP, Signature LRP)
--labellingPredsTrans _   _      []  = Set.singleton mempty
labellingPredsTrans mkH goalAF pgm = unEmbed $ do

    let goal0 = AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList skgoal]
        af0   = goal0 `mappend` AF.init sig0
        sig0  = getSignature rr0

        rr0   = mconcat [mkNewMode lrr (id, getArity sig_pl id) pp | (unlabel -> InId id, pp) <- AF.toList goal0]

    (rr1, af1, sig1) <- invariantEVPreds heuristic (rr0, af0, sig0)

    -- ("Rules added:\n" ++ unlines (map show $ Types.rules added) ) $
--    trace (unlines(map showPpr $ rules rr0) ++ "\n" ++ showPpr af0) $ return ()

    fix (invariantNewModes (invariantEVPreds heuristic) lrr) (rr1, af1, sig1)

 where
  heuristic = mkHeu mkH (prologTRS' lrr)

  pl1    = prepareProgram (addMissingPredicates pgm)
  pl'    = fmap2 (fmap (mapTermSymbols Plain) . labelGoal) pl1
  sig_pl = getSignature pl1

  lrr    = fixSymbols $ skTransform pl'
  skgoal = skTransformAF pgm goalAF

type P'   = Abstract :+: V :+: PF
type LP'  = Labelled (Expr (Abstract :+: V :+: PF))
type Pred = NotAny   :+: V :+: PF

labellingConsTrans :: forall m v. (v ~ Narradar.Var) =>
                      [FilePath] -> (String, [Mode]) -> [Clause String]
                   -> Set((PrologRules LRP v, AF_ LRP), Set LRP)
--labellingConsTrans  _ [] = return (Set.singleton mempty)
--labellingConsTrans (g,_)  pgm | g `Set.notMember` getDefinedSymbols pgm = error "labellingConsTrans: not a valid goal"
labellingConsTrans bddbddb_path (g,mm) pgm = runIt $ do
#ifdef DEBUG
   trace ("Estimated depth of " ++ show depth) $ return ()

   trace (show (text "Bddbddb produced the following patterns:"  $$ vcat (map ppr $ concat successpats)
--               $$ text "Meaningful pats are: " <> ppr filteredPats
--               $$ text "Added the clauses:" $$ Ppr.empty $$ vcat (map ppr $ Set.toList (additionalClauses `Set.difference` Set.fromList lpgm))
--               $$ text "Resulting clauses:" $$ Ppr.empty $$ vcat (map ppr $ Set.toList allClauses)))
         )) $ return ()
#endif

   (rr', af', sig') <- fix (\f -> invariantNewCons additionalRules f
                              >=> invariantEVCons  additionalRules f) (rr0, af0, sig0)
   let prologrules = Map.mapKeysWith mappend fst rr'
       modes       = Set.filter (\c -> let l = getLabel c in isJust l && l /= Just(iFun sig' c)) (getConstructorSymbols sig')
   return ((prologrules, af'), modes)

 where
  runIt = unEmbed

  abstractGoal  = abstractCompileGoal g [ m == G | m <- mm]

  depth     = maximum [ termDepth t | Pred _ tt :- _ <- pgm, t <- tt]

  cs_opts :: ComputeSuccessPatternsOpts Pred (T String :+: P')
  cs_opts = computeSuccessPatternsOpts{ pl = pgm
                                      , mb_goal = Just abstractGoal
                                      , depth
                                      , bddbddb_path
#ifdef DEBUG
                                      , verbosity = 2
#endif
                                      }

  (_dom, successpats) = unsafePerformIO $ computeSuccessPatterns cs_opts

  filteredPats = [ (p, evalTerm (const any) (\(T x) -> x) <$> tt)
                   | Pred (Al.match -> Just (Answer p)) tt <- concat successpats]

  additionalClauses = mconcat (map ( Set.fromList . fmap2 (mapPredId Plain) . mkClausesFromAPats rep_pgm) filteredPats)
                        `Set.difference`
                      Set.fromList lpgm

  (additionalRules, rr0) = runSk$ do
    rr0        <- skTransformWithM (\(Pred id tt :- _) -> (id, mapTermSymbols (fmap FunctorId) <$> tt)) lpgm
    additional <- skTransformWithM (\(Pred id tt :- _) -> (id, mapTermSymbols (fmap FunctorId) <$> tt)) (Set.toList additionalClauses)
    return (fixSymbols additional, fixSymbols rr0)

  pl'  = prepareProgram (addMissingPredicates pgm)
  lpgm = labelTerm (const True) <$$$> (mapPredId Plain <$$> pl')

  sig0 = getSignature rr0
  af0  = AF.mapSymbols Plain (skTransformAF pgm (mkGoalAF (g,mm)))
         `mappend` AF.init sig0
#ifdef DEBUG
--         `mappend` AF.singleton (Plain (InId eq)) [1]    -- Just for TESTING
#endif
         `mappend` AF.fromList [ (f,l) | f@(Labelling l _) <- Set.toList $ getConstructorSymbols sig0]

  rep_pgm = prepareProgram pgm


labellingConsAndPredsTrans :: forall m v. (v ~ Narradar.Var) =>
                              [FilePath] -> (String, [Mode]) -> [Clause String]
                           -> Set((PrologRules LRP v, AF_ LRP), Set LRP)
--labellingConsAndPredsTrans  _ [] = return (Set.singleton mempty)
--labellingConsAndPredsTrans (g,_)  pgm | g `Set.notMember` getDefinedSymbols pgm = error "labellingConsTrans: not a valid goal"
labellingConsAndPredsTrans bddbddb_path (g,mm) pgm = runIt $ do
#ifdef DEBUG
   trace ("Estimated depth of " ++ show depth) $ return ()
   trace (show(text "Bddbddb produced the following patterns:" $$ nest 2 (vcat (map ppr $ concat successpats))
--                  text "Meaningful pats are: " <> ppr filteredPats $$
--                  text "Added the clauses:" $$ Ppr.empty $$ vcat (map ppr $ Set.toList (additionalClauses `Set.difference` Set.fromList lpgm))
--                  text "Resulting clauses:" $$ Ppr.empty $$ vcat (map ppr $ Set.toList allClauses)
         )) $ return ()
#endif
   (rr1, af1, sig1) <- fix (\f -> invariantNewCons additionalRules f >=>
                                  invariantEVConsAndPreds additionalRules f >=>
                                  invariantNewModes' lrr f)
                             (rr0, af0, sig0)

   let prologrules = Map.mapKeysWith mappend fst rr1
       modes       = Set.filter (\c -> let l = getLabel c in isJust l && l /= Just(iFun sig1 c))
                                (getConstructorSymbols sig1)
   return ((prologrules, af1), modes)

 where
  runIt = unEmbed

  rr0  = mconcat [ mkNewMode' lrr (id, getArity sig_pl id) pp
                           | (f@(unlabel -> InId id), pp) <- AF.toList goal0]
  sig0 = getSignature rr0
  goal0= AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList (skTransformAF pgm (mkGoalAF (g, mm)))]
  af0  = goal0  `mappend` AF.init sig0

  abstractGoal  = abstractCompileGoal g [ m == G | m <- mm]

  depth     = maximum [ termDepth t | Pred _ tt :- _ <- pgm, t <- tt]

  cs_opts :: ComputeSuccessPatternsOpts Pred (T String :+: P')
  cs_opts = computeSuccessPatternsOpts{ pl = pgm
                                      , mb_goal = Just abstractGoal
                                      , depth
                                      , bddbddb_path
#ifdef DEBUG
                                      , verbosity = 2
#endif
                                      }

  (_dom, successpats) = unsafePerformIO $ computeSuccessPatterns cs_opts

  filteredPats = [ (p, evalTerm (const any) (\(T x) -> x) <$> tt)
                   | Pred (Al.match -> Just (Answer p)) tt <- concat successpats]

  additionalClauses = mconcat (map (Set.fromList . fmap2 labelGoal . mkClausesFromAPats rep_pl) filteredPats)
                      `Set.difference` Set.fromList lpgm

  (additionalRules, lrr) = runSk$ do
    rr         <- skTransformWithM (\(Pred id tt :- _) -> (id, mapTermSymbols (fmap FunctorId) <$> tt)) lpgm
    additional <- skTransformWithM (\(Pred id tt :- _) -> (id, mapTermSymbols (fmap FunctorId) <$> tt)) (Set.toList additionalClauses)
    return (fixSymbols additional, fixSymbols rr)

  rep_pl  = prepareProgram pgm
  pl'     = prepareProgram (addMissingPredicates pgm)
  sig_pl  = getSignature pl'
  lpgm    = labelTerm (const True) <$$$> (labelGoal <$$> pl')
  sig_lrr = getSignature lrr

mkClausesFromAPats pgm (p, apats) = clauses where
    clauses= [ Pred p' pats' :- gg
               | (h@(Pred p' pats) :- gg) <- labelTerm (const True) <$$$> pgm
               , reinject p' == p
               , Just pats' <- [zipWithM amatch pats apats]
             ]

labelGoal (Pred id tt) = Pred (Labelling [1..length tt] id) tt

-- ------------
-- Invariants
-- ------------

invariantNewModes ev lrr f (the_m, af, _)
  | Set.null new_modes = return (the_m, af, sig0)
  | otherwise          = f =<< ev =<< foldM g (the_m, af, sig0) (Set.toList new_modes)
 where
  sig0      = getSignature the_m
  new_modes =  Set.fromList [ (Labelling l s)
                             | (Labelling l (InId s)) <- Set.toList (allSymbols sig0)]
               `Set.difference` Map.keysSet the_m
  g prev@(rr0, af, sig) f@(Labelling pp id) = (prev `mappend`) `liftM` ev (rr', af', sig')
            where
              rr'  = mkNewMode lrr (id, getArity sig (InId <$> f)) pp
              sig' = getSignature (rr' `mappend` rr0)
              af'  = af `mappend` AF.init sig'

mkNewMode lrr (id,ar) pp | trace ("mkNewMode " ++ showPpr (id,pp)) False = undefined
mkNewMode lrr (id,ar) pp =
    let lid = Labelling [1..ar] id
    in (Map.singleton (Labelling pp id) $
               Set.fromList [l `setLabel` Just pp :-> r `setLabel` Just pp
                                 | (l :-> r) <- maybe (error ("mkNewMode:" ++ showPpr lid))
                                                      toList
                                                      (Map.lookup lid lrr)])

invariantNewModes' lrr f (the_m, af, sig)
  | Set.null new_modes = return (the_m, af, sig)
  | otherwise          = f (the_m', af', sig')
 where
  the_m'    = mconcat [mkNewMode' lrr (id, getArity sig (InId <$> f)) pp
                         | f@(Labelling pp id) <- Set.toList new_modes]
              `mappend` the_m
  sig'      = getSignature the_m'
  af'       = AF.init sig'
  new_modes = Set.fromList [ Labelling l s | (Labelling l (InId s)) <- Set.toList (definedSymbols sig)]
             `Set.difference` Set.map fst (Map.keysSet the_m)

mkNewMode' lrr (id,ar) pp | trace ("mkNewMode " ++ showPpr (id,pp)) False = undefined
mkNewMode' lrr (id,ar) pp =
    let lid  = Labelling [1..ar] id
        lid' = Labelling pp      id
        keys = [ k | k@(the_lid,_pats) <- Map.keys lrr, the_lid == lid]
    in Map.fromList  [ (k, Set.fromList rr)
                        | k <- keys
                        , let rr =  [ l `setLabel` Just pp :-> r `setLabel` Just pp
                                       | (l :-> r) <- maybe (error ("mkNewMode':" ++ showPpr lid'))
                                                            toList
                                                            (Map.lookup k lrr)]
                     ]
--invariantNewCons _ _ _ | trace "invariantNewCons" False = undefined
invariantNewCons new_rr f (the_m, af, sig)
  | Set.null new_cons || null (rules new_m) = return (the_m, af, sig)
  | otherwise         =    pprTrace (vcat [text "+" <+> ppr r | r <- rules new_m])  $
                        f (the_m', af', sig')
 where
  new_cons =  (Set.fromList [ id | id <- Set.toList m_cons, isFunctorId id]
              `Set.difference` Set.fromList (foldMap2 termIds (snd <$> Map.keys the_m)))
  m_cons   = getConstructorSymbols sig
  the_m'   = the_m `mappend` new_m
  new_m    = Map.fromList
              [ ( (f, pats'), rr)
               | ((f,pats), rr) <- Map.toList new_rr
               , let filtering = case Set.fromList <$> AF.lookup (InId <$> f) af of
                                   Just x -> x
                                   Nothing -> error (show( text "invariantNewCons" <+> parens(text "new_cons =" <+> ppr new_cons) <> colon <+> ppr (InId <$>f)))
               , let occurrs = [ () | (i, cc) <- zip [1..] (map termIds pats)
                                      , i `Set.member` filtering
                                      , not $ Set.null $ Set.intersection new_cons (Set.fromList cc)]
               , not (null occurrs)
               , let pats' = [ if i `Set.member` filtering && all (`Set.member` m_cons) (foldMap termIds pats)
                                  then p else resetLabels p
                               | (i,p) <- zip [1..] pats]
               ]
  af'      = af `mappend` AF.init new_m -- AF.fromList [ (c, l) | c@(Labelling l _) <- toList (getConstructorSymbols new_m)]
  sig'     = getSignature the_m'

invariantEVPreds heuristic (the_m, af, sig)
  | ((rr_pred,pred,rule@(l:->r),pos):_) <- extra
  = do (f, i) <- embed $ runHeu heuristic af r pos
       let (rr',af',sig') = fix cutEVPreds rule i rr_pred af sig f

       pprTrace (hsep$ punctuate comma $ [text "pred:"   <+> ppr pred
                                         ,text "symbol:" <+> ppr f
                                         ,text "i:"      <+> int i
                                         ,text "pos:"    <+> ppr pos
                                         ,text "rule:"   <+> ppr (AF.apply af rule)]) (return ())

       invariantEVPreds heuristic (Map.insert pred rr' the_m, af', sig')

  | otherwise  = return (the_m, af, sig)
 where
  extra = [(rr, pred, r, noteV (head ev))
             | (pred,rr) <- Map.toList the_m, r <- Set.toList rr
             , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
             , not (null ev)]

-- invariantEVCons _ _ _ | trace "invariantEVCons" False = undefined
invariantEVCons allRules f (the_m, af, sig)
  | ((k,rule@(l:->r),pos):_) <- extra =
   let (i,prefix)  = (last pos, init pos)
       Just symbol = rootSymbol (r ! prefix)
   in pprTrace (hsep $ punctuate comma $ [text "pred:"   <+> ppr (fst k)
                                         ,text "symbol:" <+> ppr symbol
                                         ,text "i:"      <+> int i
                                         ,text "prefix:" <+> ppr prefix
                                         ,text "rule:"   <+> ppr (AF.apply af rule)]) $

     f (fix cutEVCons k allRules rule (i,prefix) (the_m,af,sig) symbol)
  | otherwise  = return (the_m, af, sig)
 where
  extra = [(k, r, noteV (head ev))
            | (k, rr) <- Map.toList the_m
            , r <- Set.toList rr
            , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
            , not (null ev)
          ]


invariantEVConsAndPreds allRules f  (the_m, af, sig)
  | ((k,rule@(l:->r),pos):_) <- extra =
   let (i,prefix)  = (last pos, init pos)
       Just symbol = rootSymbol (r ! prefix)
   in pprTrace (hsep $ punctuate comma $ [text "pred:"   <+> ppr (fst k)
                                         ,text "symbol:" <+> ppr symbol
                                         ,text "i:"      <+> int i
                                         ,text "prefix:" <+> ppr prefix
                                         ,text " rule:"  <+> ppr (AF.apply af rule)]) $

     f $ fix cutEV k rule (i,prefix) (the_m,af,sig) symbol

  | otherwise  = return (the_m, af, sig)

 where
  cutEV fix k rule (i,prefix) (the_m, af, sig) f@(Labelling _lab (InId f_pred)) = (the_m', af', sig')
   where (rr', af', sig') = cutEVPreds fix rule i rr af sig f
         Just rr = Map.lookup k the_m
         the_m'  = Map.insert k rr' the_m

  cutEV ffix k rule pos st f = cutEVCons ffix' k allRules rule pos st f
    where ffix' k _ rule pos st f = ffix k rule pos st f

  extra = [(k, r, noteV (head ev))
            | (k, rr) <- Map.toList the_m
            , r <- Set.toList rr
            , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
            , not (null ev)
          ]

cutEVPreds _fix rule@(l:->r) i rr af sig f@(Labelling _lab (InId f_pred)) =
      pprTrace ( --  text "\nAdded" <+> int (Set.size added) <+> text "rules and deleted" <+> int (Set.size deleted) $$
                   vcat [text "+" <+> ppr r | r <- toList added] $$
                   vcat [text "-" <+> ppr r | r <- toList deleted]) $
--                   text "Resulting Rules and AF:" $$ vcat (map ppr $ toList rr') $$ ppr af') $
     (rr', af', sig')

  where
      (Impure (Term u@(unlabel -> UId{}) (Impure (Term g@(Labelling lab (InId gid)) vv2) : vv1))) = r
      g_arity = getArity sig g
      gl'     = assert (f==g && lab == _lab) $ Labelling (delete i lab) gid
      gl_in   = InId  <$> gl'
      gl_out  = OutId <$> gl'
      r'      = term u (term gl_in vv2 : vv1)
      changes1 = Set.insert (l:->r') . Set.delete rule
      changes3 = foldr (.) id
                        [ Set.insert outrule' . Set.delete outrule
                         | outrule@(l :-> r) <- Set.toList rr
                         , (Impure (Term u' (Impure (Term (unlabel -> OutId h) vv2) : vv1))) <- [l]
                         , u == u', assert (h == f_pred) True
                         , let outrule' = term u (term gl_out vv2 : vv1) :-> r]
      rr' = (changes1 . changes3) rr
      af' = af `mappend` AF.fromList [(gl_in, labelling gl'), (gl_out, [1..g_arity])]
      sig'= sig{definedSymbols = definedSymbols sig `mappend` Set.fromList [gl_in, gl_out],
                arity = arity sig `mappend` Map.fromList [(gl_in, g_arity), (gl_out, g_arity)]}

      common = Set.intersection rr' rr; added = rr' `Set.difference` common; deleted = rr `Set.difference` common

cutEVPreds _ _ i rr af sig f = (rr, AF.cut f i af, sig)

-- labellingPredsTrans _ af p = R.return ((convert p, convert af), [])

cutEVCons fix k allRules rule@(l:->r) (i, prefix) (the_m, af, sig) f@(unlabel -> FunctorId{})
  = case fixOutputPatterns k allRules rule (the_m, af', sig) (i,prefix) r'
               of Just res -> res
                  _        -> let Just symbol' = rootSymbol (r ! init prefix)
                              in  fix k allRules rule (last prefix, init prefix) (the_m, af, sig) symbol'
   where
    r'  = updateAt prefix r (mapRootSymbol (const f'))
    f'  = mapLabel (fmap (delete i)) f
    af' = af `mappend` AF.singleton f' (fromJust $ getLabel f')

 -- If there is no constructor, we must cut a function argument.
 -- We also take the chance to remove all the now irrelevant
 -- variants with filtered constructors.
cutEVCons _ k _ rule@(l:->r) (i, prefix) (the_m, af,sig) f@(Plain InId{})
  = pprTrace (text "deleting irrelevant patterns" <+> ppr (snd <$> irrelevant) $$
              vcat [text "-" <+> ppr r | r <- Set.toList (mconcat (Map.elems the_m) `Set.difference` mconcat(Map.elems the_m'))]

    ) $
    (the_m', AF.cut f i af, sig)
  where
    the_m'  = foldr (\k -> Map.delete k) the_m irrelevant
    irrelevant =
        [ k | k@(pred',pats) <- Map.keys the_m
          , (InId <$> pred') == f
          , let the_pat = pats !! (i-1)
          , the_pat /= resetLabels the_pat
        ]

cutEVCons _ k _ rule@(l:->r) (i, prefix) (the_m, af, sig) f = (the_m, AF.cut f i af, sig)

fixOutputPatterns k allRules rule@(l:->r) (the_m, af, sig) (i, prefix) r' =
  case Set.toList $ getInstantiationMappings allRules (r' ! init prefix) of
    -- If we are filtering an answer pattern, we need to adjust all the existing
    -- function calls matching this pattern.
    _ | Just (unlabel -> OutId call) <- rootSymbol r
      -> let the_m1  = mapAtKey k ( Set.insert (l :-> r') . Set.delete rule) the_m
             the_lhss= [ l | Just my_rules <- [Map.lookup k the_m]
                           , l :-> r       <- Set.toList my_rules
                           , (isInId <$> rootSymbol l) == Just True]

             matching_calls = Map.map
                                (Set.filter (\r -> let call = rhs r ! [1] in
                                              Prelude.any (`matches` getVariant call the_lhss) the_lhss &&
                                              Prelude.any (not.isVar) (directSubterms call)))
                                the_m1

             the_m' = Map.mapWithKey
                       (\k r_set ->
                         case Map.lookup k matching_calls of
                          Just coincidences
                           -> let newrules = Set.fromList
                                             [ l' :-> r
                                               | (_ :-> (rootSymbol -> Just uid)) <- Set.toList coincidences
                                               , l@(rootSymbol -> Just uid') :-> r <- Set.toList r_set
                                               , uid == uid'
                                               , let l' = updateAt (1 : prefix) l (mapRootSymbol (mapLabel (fmap (delete i))))
                                             ]
                              in (if not(Set.null newrules)
                                   then pprTrace (text "Adding rules to adjust existing answer patterns." $$
                                                  vcat [text "+" <+> ppr r | r <-  toList newrules])
                                   else id)
                                 Set.union newrules r_set
                      ) the_m1
         in return (the_m', af, sig)

  -- Since we are labelling a constructor used in a function call,
  -- we also need to adjust the answer patterns. There are two cases,
  -- either there is no answer pattern matching, or there are one or
  -- more.
    []   -> pprTrace (text "Wanted to introduce constructor" <+> ppr (r' ! init prefix) <+> text "but there is no matching answer pattern") $
            Nothing

    outs -> let [next_u@(lu:->ru)] =  [ rl | let Just r_set = Map.lookup k the_m
                                           , rl <- Set.toList r_set
                                           , rootSymbol(lhs rl) == rootSymbol r ]
                Impure (Term u (out0 : vv1)) = lu
                lus'     = [ term u (out0' : vv1)
                                     | out <- outs
                                     , let arg_i = last prefix
                                     , let Just label' = getLabel =<< rootSymbol (out !!(arg_i-1))
                                     , let out0' = updateAt [arg_i] out0 (mapRootSymbol (mapLabel (\_ -> Just label')))
                                   ]
                newrules = Set.fromList [lu' :-> ru | lu' <- lus']
                the_m' = mapAtKey k ( Set.insert(l :-> r')
                                    . Set.union  newrules
                                    . Set.delete rule
                                    . Set.delete next_u
                                    )
                                    the_m
            in (if not(Set.null newrules) then pprTrace (text "Adjusting the expected output in the next rule:" $$
                                                         text "-" <+> ppr next_u $$
                                                         vcat [text "+" <+> ppr r | r <- Set.toList newrules])
                                          else id) $
                return (the_m', af, sig)

--buildInstantiationMapping :: PrologRules id -> Map (GoalF id (Free f Var)) [Free f Var]
getInstantiationMappings the_m t@(rootSymbol -> Just (unlabel -> (OutId id)))
  = getInstantiationMappings the_m (mapRootSymbol (fmap (const $ InId id)) t)

getInstantiationMappings the_m goal
  = Set.fromList
    [ applySubst sigma <$> directSubterms rhs
      | ((p', pats'), rset) <- Map.toList the_m
      , getVariant (term (InId <$> p') pats') goal `Narradar.unifies` goal
      , let rules = getVariant (toList rset) goal
      , lhs <- [ l | l :-> r  <- rules
                   , (isInId <$> rootSymbol l) == Just True]
      , Just sigma <- [lhs `Narradar.unify` goal]
      , _ :-> rhs <- rules
      , (isOutId <$> rootSymbol rhs) == Just True
      ]

mapAtKey k f = Map.mapWithKey (\k' x -> if k' == k then f x else x)

resetLabels = foldTerm return f where
  f t = Impure $ mapId (mapLabel (\_ -> Just [1 .. length (Data.Foldable.toList t)])) t

{-| Abstract matching
    Takes a labelled pattern and an abstract value and restricts the
    labellings in the pattern according to the abstract value.
    It does understand multi-level patterns and abstract values.

    > amatch [_|_] static = [_|_]
    > amatch [_|_] [s|a]  = [_|_]_1
    > amatch [_|_] [a|s]  = [_|_]_2
-}
{-
amatch :: (t ~ termF lid, lid ~ (Labelled(Expr f')), MapId termF, Traversable t, HasId t lid, Eq (Expr f),
               Compound :<: f, NotVar :<: f, Prolog.Any :<: f, f' :<: f, MonadPlus m) =>
              Free t v -> Expr f -> m (Free t v)
-}
amatch pat (isNotvar -> True) = if (isVar .|. isConstant) pat then return pat
                                 else error(show (text "the analysis is not precise enough (notvar):" <+> ppr pat))
amatch pat (isAny    -> True) = if (isVar .|. isConstant) pat then return pat else mzero --  error "the analysis is not precise enough (any)"

amatch pat _  | isVar pat = return pat

amatch pat@(fmap unlabel . getId -> Just c) apat@(Al.match -> Just (Compound c' tt'))
-- > amatch [:pterm| c tt] [:oexpr| c' tt'] =
   = do
        guard (reinject c == c' && length (directSubterms pat) == length tt')
        let ll = [ i | (i,a) <- (zip [1..] tt'), not (isAny a)]
        let pat1 = mapRootSymbol (\_->Labelling ll c) pat
        pat' <- evalTerm return2 (\tt -> liftM Impure $ unsafeZipWithGM (flip amatch) tt' tt) pat1
        return pat'
amatch _ _ = fail "amatch: patterns didn't match"


{-
       newCons' = Set.fromList [ compound (reinject f :: Expr (T String :+: P')) args
                                       | Labelling l (FunctorId f)  <- concatMap (Set.toList . snd) newCons
                                       , f `Set.member` getConstructorSymbols sig_pl
                                       , let sl   = Set.fromList l
                                       , let args = [if i `Set.member` sl then notvar else any
                                                      | i <- iFun sig_pl f]
                                       ]

       meaningfulPats = [ (p :: String, evalTerm (error "labellingConsTrans/meaningful pats: the impossible happened ") (\(T x) -> x) <$> tt)
                          | Pred (Al.match -> Just (Answer p)) tt <- concat successpats `const` abstractGoal
                          , let tt' =  [ pat | Impure (T pat) <- tt, not (isNotvar pat), not (isAny pat)]
                          , all (`Set.member` newCons') tt'
                          , not (null tt')
                          ]

#ifdef DEBUG
   trace (show ( -- text "Bddbddb produced the following patterns:" $$ vcat (map ppr $ concat successpats) $$
                      text "Meaningful pats are: " <> ppr meaningfulPats)) $ return ()
#endif
-}

{-
-- | Abstract matching, well sort of
--
-- > amatches [_|_]    static  == True
-- > amatches [_|_]    cons_aa == True
-- > amatches X        any     == True
-- > amatches [_|_]    any     == True
amatches :: (Eq id, HasId t id, Foldable t,
             T id :<: f, Compound :<: f, Static :<: f, Prolog.Any :<: f) =>
             Free t v -> Expr f -> Bool
amatches _                                              (isAny -> True)    = True
amatches _                        (isStatic -> True) = True
amatches t@(getId -> Just (Plain (FunctorId c)))        (Al.match -> Just (Compound (Al.match -> Just(T c')) ll'))
 = length (directSubterms t) == length ll' && c == c' && all (not . isAny) ll'
amatches t@(getId -> Just (Labelling ll (FunctorId c))) (Al.match -> Just (Compound (Al.match -> Just(T c')) ll'))
            = c == c' && ll `agreesWith` ll' && and (zipWith amatches (directSubterms t) ll')
    where agreesWith ll aa = and [ case a of
                                _ | isAny a   -> i `notElem` ll
                                  | otherwise -> i `elem` ll
                               | (i,a) <- zip [1..] aa
                             ]
amatches _ _ = False
-}
{-
fixSymbols' :: Ord v => NarradarTRS (PrologId (Expr (T (Labelled String) :+: P))) v -> NarradarTRS LRP v
fixSymbols' (PrologTRS rr sig) = prologTRS' rr'  where
  rr'         = Set.map (second (fmap (mapTermSymbols fixSymbol))) rr
  fixSymbol t = case runWriter (T.mapM (foldExprM removeLabelF) t) of
                  (t', Nothing) -> Plain t'
                  (t', Just ll) -> Labelling ll t'


class (Functor f, Functor g) => RemoveLabelF f g where removeLabelF :: MonadWriter (Maybe [Int]) m => f (Expr g) -> m(Expr g)
instance (RemoveLabelF f1 g, RemoveLabelF f2 g)  => RemoveLabelF (f1 :+: f2) g where
   removeLabelF (Inl l) = removeLabelF l
   removeLabelF (Inr r) = removeLabelF r
instance (a :<: g) => RemoveLabelF a g where removeLabelF = return . inject . fmap reinject
instance (T id :<: g) => RemoveLabelF (T (Labelled id)) g where
   removeLabelF (T (Labelling ll x)) = tell (Just ll) >> return (mkT x)
-}

-- ----------
-- Auxiliary
-- ----------

iFun sig f = [1.. getArity sig f]

isConstant = null . directSubterms

--fixSymbols :: (Ord a, Ord v) => PrologRules (PrologId (Labelled a)) v -> PrologRules (Labelled (PrologId a)) v
fixSymbols = (Map.map . Set.map) (fmap (mapTermSymbols fixLabelling))

fixLabelling :: Ord a => PrologId (Labelled a) -> Labelled (PrologId a)
fixLabelling t = case toList t of  -- hack to get to the id inside the PrologId
                  [Plain     _]   -> Plain       pt
                  [Labelling l t] -> Labelling l pt
                  [] {- so UId -} -> Plain pt
     where [lt] = toList t
           pt   = fmap unlabel t

termDepth = foldTerm (const 0) f where
    f Wildcard = 0
    f tf = 1 + F.maximum (0 : toList tf)
