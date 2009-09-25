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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TransformListComp #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Narradar.Types.Problem.Prolog where

import Control.Applicative
import Control.Arrow (first, second, (***))
import Control.Exception (assert)
import Control.Monad.Free.Zip (zipFree)
import Control.Monad.Identity (Identity(..))
import Control.Monad.List   (ListT(..))
import Control.Monad.Reader (MonadReader(..), Reader(..))
import Control.Monad.RWS (RWST, execRWST)
import Control.Monad.State
import Control.Monad.Writer (MonadWriter(..), Writer(..), WriterT(..), Any(..))
import Control.Monad.Supply
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.AlaCarte as Al hiding (Note)
import Data.AlaCarte.Ppr hiding (Note)
import Data.Char (isSpace)
import Data.List as List hiding (any,notElem)
import Data.Maybe
import Data.Monoid      (Monoid(..))
import Data.Foldable    (Foldable(foldMap,foldr), toList, notElem)
import Data.Traversable (Traversable(traverse))
import qualified Data.Foldable    as F
import qualified Data.Traversable as T
import Data.Map (Map)
import Data.Set (Set)
import Data.UniqueList (UniqueList)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.UniqueList as UList
import Language.Haskell.TH (runIO)
import Text.ParserCombinators.Parsec (parse)
import System.IO.Unsafe
import GHC.Exts (the)

import Data.DeriveTH
import Data.Derive.Foldable
import Data.Derive.Functor
import Data.Derive.Traversable

import Data.Term hiding (find)
import Data.Term.Rules
import Data.Term.Var as Prolog (Var(VName, VAuto))
import qualified Language.Prolog.Syntax as Prolog

import TRSTypes (Mode(..))

import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Types.ArgumentFiltering (AF_, MkHeu, mkHeu, ApplyAF(..), PolyHeuristic, Heuristic(..), simpleHeu, innermost)
import Narradar.Types.Goal
import Narradar.Types.DPIdentifiers
import Narradar.Types.PrologIdentifiers
import Narradar.Types.Labellings
import Narradar.Types.TRS
import Narradar.Types.Term as Narradar
import Narradar.Types.Var  as Narradar
import Narradar.Types.Problem
import Narradar.Types.Problem.InitialGoal
import Narradar.Types.Problem.Narrowing
import Narradar.Framework
import Narradar.Framework.Ppr as Ppr
import Narradar.Utils


import Language.Prolog.Syntax (Program, Program'', Clause, ClauseF(..), cHead, cBody, GoalF(..),
                               TermF(Cons, Nil, Tuple, Wildcard, String, Int, Float), mapPredId)
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

import Prelude hiding (and,or,any,notElem,pi)
import qualified Prelude as P


type PF' id = PrologT :+: PrologP :+: T id
type PF   = PF' String
type P    = Expr PF
type RP   = PrologId P
type LP   = Labelled P
type DRP  = Identifier RP
type LRP  = Labelled RP
type DLRP = Identifier LRP

-- -----------------
-- Prolog Problems
-- -----------------
-- * NOT dp problems

data PrologProblem id = PrologProblem {goals::[Goal id], program::Prolog.Program id}
prologProblem      = PrologProblem


instance Ord id => HasSignature (PrologProblem id) where
  type SignatureId (PrologProblem id) = id
  getSignature (PrologProblem _ clauses) = getSignature clauses

instance Pretty (PrologProblem String) where
    pPrint PrologProblem{..} =
            text "Prolog problem." $$
            text "Clauses:" <+> pPrint program $$
            text "Goals:" <+> pPrint goals


-- ------------------------------------------
-- Representation of Prolog clauses as rules
-- ------------------------------------------

data ClauseRules a =
        FactRule    {inRule :: a}
      | ClauseRules {inRule :: a, outRules' :: [a], uRules :: [a]}
 deriving (Eq, Ord, Show)

outRules (FactRule r) = [r]
outRules rr = outRules' rr

{-
instance Monoid (ClauseRules a) where
  mappend cr1 cr2 = cr1{uRules = uRules cr1 ++ uRules cr2}
  mempty = ClauseRules
-}

-- | Left biased set union
mergeRules r1@FactRule{} r2@FactRule{} = r1
mergeRules cr1 cr2 = cr1{ uRules    = nubBy equiv2' (uRules cr1 ++ uRules cr2)
                        , outRules' = nubBy equiv2' (outRules cr1 ++ outRules cr2)}

successRules (FactRule _) = []
successRules ClauseRules{..} = outRules' ++ uRules

callRules (FactRule _) = []
callRules ClauseRules{..} = inRule : uRules

getURules u cr = do
   r@(lu:->_) <- successRules cr
   guard(rootSymbol lu == Just u)
   return r

addRules rr cr = P.foldr f cr rr where
  f rule cr = if Just True == (isOutId <$> rootSymbol (rhs rule))
                then cr{outRules' = rule : outRules cr}
                else cr{uRules   = rule : uRules cr}

updateByLhs  l = updateByLhss (Set.singleton l)
updateByLhss ll f = fmap f'
   where
     f' rule = if lhs rule `Set.member` ll then right f rule else rule

mapOut f (FactRule r) = FactRule (f r)
mapOut f rr@ClauseRules{..} = rr{outRules' = fmap f outRules'}

deleteCalls calls ccrr = ccrr { uRules   = filter ((`Set.notMember` calls) . lhs) (uRules ccrr)
                              , outRules' = filter ((`Set.notMember` calls) . lhs) (outRules ccrr)
                              }

updateAnswer  ui f = updateAnswers (Set.singleton ui) (\r -> [f r])
updateAnswers uis f (FactRule (l:->r)) = case f r of [r'] -> FactRule (l:->r')
updateAnswers uis f ccrr =
           ccrr{ outRules' = concatMap f' (outRules ccrr)
               , uRules   = concatMap f' (uRules   ccrr)
               }
 where
  f' (l:->r) = case getUId =<< rootSymbol l of
                  Just u_i | u_i `Set.member` uis
                           -> [l' :-> r | l' <- f l]
                  _        -> [l  :-> r]

instance HasRules f v (ClauseRules (Rule f v)) where rules = toList

instance (Foldable f, HasId f) => HasSignature (ClauseRules (Rule f v))
 where
    type SignatureId (ClauseRules (Rule f v)) = TermId f
    getSignature = getSignature . rules

instance (Foldable f, HasId f) => HasSignature [ClauseRules (Rule f v)]
  where
    type SignatureId  [ClauseRules (Rule f v)] = TermId f
    getSignature = getSignature . foldMap rules

instance (Traversable t, GetFresh t v thing) => GetFresh t v (ClauseRules thing)  where getFreshM = getFreshMdefault
instance (Ord k, Traversable t, GetFresh t v thing) => GetFresh t v (Map k thing) where getFreshM = getFreshMdefault
--instance (Traversable t, GetFresh t v thing1, GetFresh t v thing2) => GetFresh t v (thing1, thing2) where
--    getFreshM (t1,t2) = do {t1' <- getFreshM t1; t2'<- getFreshM t2; return (t1',t2')}

instance (Pretty id, Pretty v) => Pretty (ClauseRules (RuleN id v)) where pPrint = vcat . map pPrint . rules


type PrologRules id v = Map (Prolog.Clause'' (WithoutPrologId id) (TermN (WithoutPrologId id) v))
                            (ClauseRules (RuleN id v))

prologTRS'' :: (RemovePrologId id, Ord id, Ord v) => PrologRules id v -> Signature id -> NTRS id v
prologTRS'' pr sig = PrologTRS pr' sig where
    pr' = (Map.mapKeysWith mappend (\(Pred h _:-_) -> h) . Map.map (Set.fromList . toList)) pr

-- --------------
-- Processors
-- --------------

prologP_sk :: ( Monad m
              , Info info PrologToNarrowingProof
              , Info info (PrologProblem String)
              ) =>
              PrologProblem String
           -> Proof info m (NarradarProblem (InitialGoal (Narradar.TermF DRP) CNarrowing)
                                            (Narradar.TermF DRP))

prologP_sk p0@PrologProblem{..} =
   andP PrologToTRSSKNarrowingProof p0
     [ mkNewProblem (initialGoal [IdFunction <$> skTransformGoal goal] CNarrowing) sk_p
         | let sk_p          = prologTRS'' rr (getSignature rr)
               rr            = skTransformWith id (prepareProgram $ addMissingPredicates program)
         , goal            <- goals
         , let goalAF        = skTransformAF program (mkGoalAF goal)
               af_groundinfo = AF.init sk_p `mappend` goalAF
     ]
{-
prologP_labelling_sk :: (PolyHeuristicN heu LRP, PolyHeuristicN heu DLRP, MonadFree ProofF m, v ~ Narradar.Var) =>
                        MkHeu heu -> PrologProblem v -> m (Problem DLRP v)
prologP_labelling_sk mkHeu p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingSKP [] :: ProcInfo LRP) p0
  | otherwise  = mprod problems
  where problems = do
                       goal <-goals
                       let goal_lps = AF.mapSymbols' (flip Labelling) (skTransformAF program goal)
                       (prolog_rr, pi, sig) <- toList $ labellingPredsTrans mkHeu goal program
                       let trs   = prologTRS'' prolog_rr sig
                           pp'   = mkGoalProblem mkHeu GNarrowingModes{pi, goal = goal_lps} trs
                           modes = snub [ p | Pred p _ :- _ <- Map.keys prolog_rr]
                       return $ orP (LabellingSKP modes) p0 (map return pp')


prologP_labelling_cons :: (MonadFree ProofF m, v ~ Narradar.Var) =>
                        PrologProblem v -> m (Problem DLRP v)
prologP_labelling_cons p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingCP [] :: ProcInfo LRP) p0
  | otherwise  = mprod problems
  where problems = do
                       g      <- goals
                       (f,ii) <- AF.toList g
                       let query = (f, [ if i `elem` ii then G else V | i <- [1..getArity program f]])
                           goal  = AF.mapSymbols Plain (skTransformAF program g)
                       (trs, pi, sig, modes) <- toList $ labellingConsTrans query program
                       let pp'     = mkGoalProblem (simpleHeu innermost) GNarrowingModes{pi, goal} (tRS' (nubBy equiv' $ rules trs) sig)
                           newCons = Set.toList modes
                       return $ orP (LabellingCP newCons) p0 (map return pp')

{-
prologP_labelling_all :: (MonadFree ProofF m, v ~ Narradar.Var) =>
                        [FilePath] -> PrologProblem v -> m (Problem DLRP v)
prologP_labelling_all paths p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingCP [] :: ProcInfo LRP) p0
  | otherwise  = mprod problems
  where problems = do
                       g      <- goals
                       (f,ii) <- AF.toList g
                       let query = (f, [ if i `elem` ii then G else V | i <- [1..getArity program f]])
                           goal  = AF.mapSymbols Plain (skTransformAF program g)
                       ((trs, pi), modes) <- Set.toList $ labellingConsAndPredsTrans paths query program
                       let pp'     = mkGoalProblem (simpleHeu innermost) GNarrowingModes{pi, goal} (prologTRS'' trs)
                           newCons = Set.toList modes
                       return $ orP (LabellingCP newCons) p0 (map return pp')
-}
-}
-- -------
-- Proofs
-- -------

data PrologToNarrowingProof = PrologToTRSSKNarrowingProof | PrologToTRSSKInfinitaryProof | PrologToTRSLabellingInfinitaryProof
  deriving (Eq, Show)

instance Pretty PrologToNarrowingProof where
  pPrint PrologToTRSSKInfinitaryProof = text "Termination of LP as termination of Infinitary Constructor Rewriting" $$
                                     text "(Schneider-Kamp transformation)"
  pPrint PrologToTRSSKNarrowingProof  = text "Termination of LP as termination of Narrowing proof" $$
                                     text "(Schneider-Kamp transformation)"


-- ---------
-- Analysis
-- ---------
inferType PrologProblem{program} = infer program

-- ----------------
-- Transformations
-- ----------------

skTransform :: (Ord id, Ord v, Pretty id) => [Prolog.Clause'' id (TermN id v)] -> PrologRules (PrologId id) v
skTransform = runSk . skTransformWithM id

--skTransformWith :: (Prolog.Clause'' id (TermN id v) -> ) -> [Prolog.Clause'' id (TermN id v)] -> PrologRules' (PrologId id) v
skTransformWith  mkIndex = runSk . skTransformWithM mkIndex


skTransformWithM mkIndex clauses = do
  clauseRules <- mapM (runClause . toRule) clauses
  return (Map.fromList clauseRules)
 where   -- The counter for u_i is global,
         -- the list of vars is local to each clause.
       runClause = (`evalStateT` mempty)

       toRule c@(Pred id tt :- (filter (/= Cut) -> [])) = do
         let tt' = mapTermSymbols FunctorId <$> tt
         return (mkIndex c, FactRule (term (InId id) tt' :-> term (OutId id) tt'))

       toRule c@(Pred id tt :- (filter (/= Cut) -> gg)) = do
         let tt' = mapTermSymbols FunctorId <$>  tt
             gg' = mapTermSymbols FunctorId <$$> gg
         modify (getVars tt' `mappend`)
         rhs_0  <- mkRhs (head gg')
         mid_r  <- forM (gg' `zip` tail gg') $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg')
         let r_0 = term (InId id) tt' :-> rhs_0
             r_n = lhs_n :-> term (OutId id) tt'
         return (mkIndex c, ClauseRules r_0 [r_n] mid_r)

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


class (Ord id, Ord id') => SkTransformAF id id' | id -> id' where
    skTransformAF :: (HasSignature sig, SignatureId sig ~ id) => sig -> AF_ id -> AF_ id'
    skTransformGoal :: Goal id -> Goal id'

instance SkTransformAF String RP where
  skTransformAF sig = AF.mapSymbols (\f -> if f `Set.member` getDefinedSymbols sig
                                         then InId (mkT f)
                                         else FunctorId (mkT f))
  skTransformGoal = fmap (InId . mkT)

instance SkTransformAF (Labelled String) LRP where
  skTransformAF sig = AF.mapSymbols (\f@(Labelling l t) -> if f `Set.member` getDefinedSymbols sig
                                         then Labelling l (InId (mkT t))
                                         else Labelling l (FunctorId (mkT t)))
  skTransformGoal = fmap2 (InId . mkT)

prepareProgram :: Program id -> Program'' (Expr (PF' id)) (TermN (Expr (PF' id)) Narradar.Var)
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

{-
labellingPredsTrans :: forall heu v.
                       (PolyHeuristic heu LRP, v ~ Narradar.Var) =>
                          MkHeu heu -> AF_ String -> Prolog.Program String
                       -> Set(PrologRules LRP v, AF_ LRP, Signature LRP)
--labellingPredsTrans _   _      []  = Set.singleton mempty
labellingPredsTrans mkH goalAF pgm = unEmbed $ do

    let goal0 = AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList skgoal]
        af0   = goal0 `mappend` AF.init sig0
        sig0  = getSignature rr0

        rr0   = mconcat [mkNewMode lrr (id, getArity sig_pl id) pp | (unlabel -> InId id, pp) <- AF.toList goal0]

    (rr', af', sig', _) <- fix (\f -> invariantEVPreds heuristic f >=> invariantNewModes f) (rr0, af0, sig0, lrr)
    return (rr',af',sig')

 where
  heuristic = mkHeu mkH (prologTRS'' lrr (getSignature lrr))

  pl1    = prepareProgram (addMissingPredicates pgm)
  pl'    = fmap2 (fmap (mapTermSymbols Plain) . labelGoal) pl1
  sig_pl = getSignature pl1

  lrr    = fixSymbols $ skTransform pl'
  skgoal = skTransformAF pgm goalAF

type P'   = Abstract :+: V :+: PF
type LP'  = Labelled (Expr (Abstract :+: V :+: PF))
type Pred = NotAny   :+: V :+: PF


labellingConsTrans :: forall m v. (v ~ Narradar.Var) =>
                      Goal String -> [Clause String]
                   -> Set(PrologRules LRP v, AF_ LRP, Signature LRP, Set LRP)
--labellingConsTrans  _ [] = return (Set.singleton mempty)
--labellingConsTrans (g,_)  pgm | g `Set.notMember` getDefinedSymbols pgm = error "labellingConsTrans: not a valid goal"
labellingConsTrans goal pgm = Set.singleton $ runIdentity $ do
   let st0           = prologMState rr0 goalAF
   (st'@PrologMState{prologM_sig},log)  <- fix (\f -> fix invariantEVCons >> invariantNewCalls f)
                                           `execPrologM` st0

   let modes = Set.filter (\c -> let l = getLabel c in isJust l && l /= Just(iFun prologM_sig c))
                          (getConstructorSymbols prologM_sig)

       prologTRS = Map.mapKeys (\(Pred p _ :- gg,tt) -> Pred p tt :- gg) (prologM_rr st')

   assert (null $ foldMap extraVars $ AF.apply (prologM_af st') $ rules prologTRS) $
    trace (unlines log) $
    return (prologTRS, prologM_af st', prologM_sig, modes)

 where
  rr0  = fixSymbols $ skTransformWith (\c@(Pred _ tt :- _) -> (c,tt)) lpgm
  pl'  = prepareProgram (addMissingPredicates pgm)
  lpgm = labelTerm (const True) <$$$> (mapPredId Plain <$$> pl')
  goalAF  = AF.mapSymbols Plain (skTransformAF pgm (mkGoalAF goal))



{-
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
--                  text "Added the clauses:" $$ Pretty.empty $$ vcat (map ppr $ Set.toList (additionalClauses `Set.difference` Set.fromList lpgm))
--                  text "Resulting clauses:" $$ Pretty.empty $$ vcat (map ppr $ Set.toList allClauses)
         )) $ return ()
#endif
   (rr1, af1, sig1,_) <- fix (\f -> invariantNewCons additionalRules f >=>
                                  invariantEVConsAndPreds additionalRules f >=>
                                  invariantNewModes f)
                             (rr0, af0, sig0, lrr)

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
                                      , smart   = True
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
-}
labelGoal (Pred id tt) = Pred (Labelling [1..length tt] id) tt

-- ------------
-- Invariants
-- ------------

invariantNewModes f (the_m, af, sig, lrr)
  | Set.null new_modes = return (the_m, af, sig0, lrr)
  | otherwise          = f (the_m', af', sig', lrr)
 where
  sig0      = getSignature the_m
  new_modes =  Set.fromList [ (Labelling l s)
                             | (Labelling l (InId s)) <- Set.toList (allSymbols sig0)]
               `Set.difference`
               Set.map (\(Pred id _ :- _) -> id) (Map.keysSet the_m)
  the_m' = the_m `mappend` foldMap g new_modes
  sig'   = getSignature the_m'
  af'    = af `mappend` AF.init sig'
  g id@(Labelling pp s) = mkNewMode lrr (s, getArity sig (InId <$> id)) pp

mkNewMode lrr (id,ar) pp | trace ("mkNewMode " ++ showPpr (id,pp)) False = undefined
mkNewMode lrr (id,ar) pp = the_m
  where lid   = Labelling pp id
        the_m = Map.fromList
                [ (Pred lid tt :- gg, mapRootSymbol (mapLabel (const $ Just pp)) <$$> rr)
                   | (Pred p tt :- gg, rr) <- Map.toList lrr
                   , p == Labelling [1..ar] id]
{-
--invariantNewCons _ _ _ | trace "invariantNewCons" False = undefined
invariantNewCons f (the_m, af, sig, all_rr)
  | Set.null new_cons || null (rules new_m) = return (the_m, af, sig, all_rr)
  | otherwise         =    pprTrace (vcat [text "+" <+> ppr r | r <- rules new_m]) $
                        f (the_m', af', sig', all_rr)
 where
  new_cons =  (Set.fromList [ id | id <- Set.toList m_cons, isFunctorId id]
              `Set.difference` Set.fromList (foldMap2 termIds (snd <$> Map.keys the_m)))
  m_cons   = getConstructorSymbols sig
  the_m'   = the_m `mappend` new_m
  new_m    = Map.fromList
              [ ( (f, pats'), rr)
               | ((f,pats), rr) <- Map.toList c_rr
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


invariantNewCons f (the_m, af, sig, all_rr)
  | Set.null new_cons || null (rules new_m) = return (the_m, af, sig, all_rr)
  | otherwise = f (traceUpdates (text "inserting new rules") the_m the_m', af', sig', all_rr)
 where
  -- NOTE: Can use the assumption that there will be only one new constructor to make this more efficient
  new_cons =  (Set.fromList [(r,id) | r <- rules the_m, id <- foldMap termIds r, isFunctorId id]
              `Set.difference`
               Set.fromList (foldMap2 termIds (snd <$> Map.keys the_m)))
  the_m'   = the_m `mappend` new_m
  new_m    = foldMap (computeNewRules new_m) new_cons
  af'      = af `mappend` AF.init new_m -- AF.fromList [ (c, l) | c@(Labelling l _) <- toList (getConstructorSymbols new_m)]
  sig'     = getSignature the_m'
-}

invariantEVPreds heuristic f (the_m, af, sig, lrr)
  | ((rr_pred,c,rule@(l:->r),pos):_) <- extra
  = do (pf, i) <- embed $ runHeu heuristic af r pos
       let (rr',af',sig') = fix cutEVPreds rule i rr_pred af sig pf

       pprTrace (hsep$ punctuate comma $ [text "pred:"   <+> pPrint (Prolog.pred $ cHead c)
                                         ,text "symbol:" <+> pPrint pf
                                         ,text "i:"      <+> int i
                                         ,text "pos:"    <+> pPrint pos
                                         ,text "rule:"   <+> pPrint (AF.apply af rule)]) (return ())

       f (Map.insert c rr' the_m, af', sig', lrr)

  | otherwise  = return (the_m, af, sig,lrr)
 where
  extra = [(rr,c, r, noteV (head ev))
             | (c,rr) <- Map.toList the_m, r <- toList rr
             , let ev = extraVars (AF.apply af (annotateWithPosV `fmap` r))
             , not (null ev)]

-- invariantEVCons _ _ _ | trace "invariantEVCons" False = undefined
invariantEVCons f = do
  extra <- runListT $ do
              (k, rr) <- ListT (Map.toList <$> getRR)
              r       <- li $ toList rr
              ev      <- extraVars <$> lift(applyAF (annotateWithPosV `fmap` r))
              guard  (not (null ev))
              return (k, r, noteV (head ev))

  case extra of
   ((k,rule@(l:->r),pos):_) ->  do

     rule' <- applyAF rule
     let (i,prefix)  = (last pos, init pos)
         Just symbol = rootSymbol (r ! prefix)
     traceM (hsep $ punctuate comma $ [text "pred:"   <+> pPrint (Prolog.pred $ cHead $ fst k)
                                      ,text "symbol:" <+> pPrint symbol
                                      ,text "i:"      <+> int i
                                      ,text "prefix:" <+> pPrint prefix
                                      ,text "rule:"   <+> pPrint rule'])

     fix cutEVCons k rule pos >> f

   otherwise -> return ()

invariantNewCalls fix = do
  kk <- getKK
  rr <- getRR
  things <- runListT $ do
    (k_call, p_rr_call) <- ListT (Map.toList <$> getRR)
    _ :-> r_call <- li $ callRules p_rr_call
    (k, p_rr) <- ListT (Map.toList <$> getDB)
    let l :-> _ = inRule p_rr
    sigma <- unify' l (r_call ! [1])
--    lift updateSignature
--    lift updateAF
    ((c,tt), p_rr') <- lift $ instantiatePM sigma k p_rr
    guard ((c, EqModulo tt) `UList.notElem` kk)
    return ((c,tt), p_rr')

  let pp = [ Pred p tt | ((c@(Pred p _ :- _), tt), _) <- things, (c, EqModulo tt) `UList.notElem` kk]
  traceUpdatesM (text "Adding clauses for calls" <+> pPrint pp) $  mapM (uncurry appendRR) things
  kk' <- getKK
  rr' <- getRR

--  if kk == kk' then return () else fix
  if kk == kk' then assert (rr == rr') (return ()) else fix


{-
invariantEVConsAndPreds cRules f st@(the_m, af, sig, all_rr)
  | ((k,rule@(l:->r),pos):_) <- extra =
   let (i,prefix)  = (last pos, init pos)
       Just symbol = rootSymbol (r ! prefix)
       (the_m', af', sig') = fix cutEV k rule (i,prefix) (the_m, af, sig) symbol
   in pprTrace (hsep $ punctuate comma $ [text "pred:"   <+> pPrint (fst k)
                                         ,text "symbol:" <+> pPrint symbol
                                         ,text "i:"      <+> int i
                                         ,text "prefix:" <+> pPrint prefix
                                         ,text " rule:"  <+> pPrint (AF.apply af rule)]) $

     f (the_m', af', sig', all_rr)

  | otherwise  = return (the_m, af, sig, all_rr)

 where
  cutEV fix k rule (i,prefix) (the_m, af, sig) f@(Labelling _lab (InId f_pred)) = (the_m', af', sig')
   where (rr', af', sig') = cutEVPreds fix rule i rr af sig f
         Just rr = Map.lookup k the_m
         the_m'  = Map.insert k rr' the_m

  cutEV ffix k rule pos st f = st'
    where st' = cutEVCons ffix' k cRules rule pos st f
          ffix' k _ rule pos st f = ffix k rule pos st f

  extra = [(k, r, noteV (head ev))
            | (k, rr) <- Map.toList the_m
            , r <- Set.toList rr
            , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
            , not (null ev)
          ]
-}

cutEVPreds _fix rule@(l:->r) i rr af sig f@(Labelling _lab (InId f_pred))
  = (traceUpdates Ppr.empty rr rr', af', sig')
  where
      (Impure (Term u@(unlabel -> UId u_i) (Impure (Term g@(Labelling lab (InId gid)) vv2) : vv1))) = r
      g_arity = getArity sig g
      gl'     = assert (f==g && lab == _lab) $ Labelling (delete i lab) gid
      gl_in   = InId  <$> gl'
      gl_out  = OutId  <$> gl'
      r'      = term u (term gl_in vv2 : vv1)

      rr'     = updateByLhs  l   (const r')
              $ updateAnswer u_i ((updateAt [1] (mapRootSymbol (mapLabel (fmap (delete i))))))
              $ rr

      af'     = af `mappend`
                AF.fromList [(gl_in, labelling gl'), (gl_out, [1..g_arity])]
      sig'    = sig{definedSymbols = definedSymbols sig `mappend` Map.fromList [(gl_in, g_arity), (gl_out, g_arity)]}

cutEVPreds _ _ i rr af sig f = (rr, AF.cut f i af, sig)

-- labellingPredsTrans _ af p = R.return ((convert p, convert af), [])

cutEVCons fix k rule@(l:->r) pos
  | FunctorId{} <- unlabel f
  = do modifySig $ \sig -> sig {Narradar.constructorSymbols =
                                 Map.insert f' (getArity sig f) (Narradar.constructorSymbols sig)}
       extendAF (AF.singleton f' (fromJust $ getLabel f'))
       modifyDB_at k (updateByLhs l (const r'))
       when ((isOutId <$> rootSymbol r) == Just True || head pos == 1) $ fixOutputPatterns k pos r'

 -- If we must cut a predicate argument,
 -- then take the chance to remove all the now irrelevant
 -- variants with filtered constructors.
  | InId{} <- unlabel f
  = do
{-
       cc <- getClauses
       let irrelevant =
            [ k | k@(Pred pred' pats :- _) <- cc
                , (InId <$> pred') == f
                , let the_pat = pats !! (i-1)
                , the_pat /= resetLabels the_pat
            ]
       traceUpdatesM (text "deleting irrelevant patterns" <+> pPrint ((args . cHead) <$> irrelevant)) $
        modifyRR' (\x -> P.foldr Map.delete x irrelevant)
-}
       cutAF f i

  | otherwise = cutAF f i

  where
    i      = last pos
    Just f = rootSymbol (r ! init pos)
    r'     = updateAt (init pos) (mapRootSymbol (mapLabel (fmap (delete i)))) r
    f'     = mapLabel (fmap (delete i)) f


-- fixOutputPatterns k rule pos r' | pprTrace (text "fixOutputPatterns" <+> pPrint r') False = undefined
fixOutputPatterns  k pos r' = traceUpdatesM (text "Fixing success patterns for" <+> pPrint r' <+> text "at pos" <+> pPrint pos) $ fixOutputPatterns' k pos r'
--fixOutputPatterns' k pos r | pprTrace (text "Fix output patterns for" <+> pPrint r <+> text "at pos" <+> pPrint pos) False = undefined
fixOutputPatterns' k pos r'

    -- Firt case, no need to do anything.
  | Just f <- rootSymbol =<< r' !* init pos
  , last pos `elem` labelling f
  = return()

    -- If we are filtering an answer pattern, we need to adjust all the existing
    -- function calls matching this pattern.
  | Just (unlabel -> OutId{} ) <- rootSymbol r' = do

    the_lhs <- (lhs.inRule) <$> lookupDB k

    matching_calls <- mapRR
                      (\rr ->
                       [ fromJust (getUId uid)
                         | l :-> Impure (Term uid (call : _)) <- callRules rr
                         , (the_lhs  `unifies'` call) &&
                           P.any (not.isVar) (directSubterms call)]
                      )
    modifyDB
          (\k p_rules ->
               let lhss = (Set.fromList $ join $ maybeToList $ Map.lookup k matching_calls)
                   newrules =
                    updateAnswers lhss
                                  -- ((:[]) . updateAt (1 : init pos) (mapRootSymbol (mapLabel (fmap (delete (last pos))))))
                                  (\r -> case updateAt' (1 : init pos) (mapRootSymbol (mapLabel (fmap (delete (last pos))))) r of
                                          Nothing     -> [r]
                                          Just (r',_) -> [r']
                                  )
                                  p_rules
               in if (not $ Set.null lhss) then mergeRules newrules p_rules else p_rules
          )

    deriveCallsForOutput k r' pos

  | otherwise
  -- Since we are labelling a constructor used in a function call,
  -- we also need to adjust the answer patterns. There are two cases,
  -- either there is no answer pattern matching, or there are one or more.

  -- There are no matching answer patterns: we need to compute them.
  = do -- r is of the form u_i(p_in(..),..)
    outs  <- Set.toList <$> getInstantiationMappings (tail pos) (r' ! [1])
    fixOuts k (fromJust $ rootSymbol r') outs
--    modifyDB_at k (const p_rr')
{-
fixWithOuts = fixOutsByCopyLabel

fixOutsByCopyLabel u_i outs p_rules =
   let new_lhss = Map.fromList $ do
                    next_u@(lu:->ru) <- getURules u_i p_rules
                    let Impure (Term u (Impure (Term p_out out0) : vv1)) = lu
                        lus' = [ term u (term p_out out' : vv1)
                                     | Impure (Term p_out' out) <- outs
                                     , out' <- zipWithM copyLabelling out0 out
                               ]
                    return (lu, lus')

   in updateAnswers (Set.map (fromJust . (rootSymbol >=> getUId))
                             (Map.keysSet new_lhss))
                    (\l -> fromJust $ Map.lookup l new_lhss)
                    p_rules
-}
fixOuts = fixOutsByInstantiation
fixOutsByInstantiation k u_i outs = ignore$ runListT $ do
   next_u@(lu:->ru) <- ListT (getURules u_i <$> lookupDB k)
   out              <- li outs
--   sigma            <- unifyPM (lu ! [1]) out
   lift $ modifyDB_at k
            (updateAnswers (Set.singleton $ fromJust $ getUId u_i) ((:[]) . updateAt [1] (const out)))


--buildInstantiationMapping :: PrologRules id -> Map (GoalF id (Free f Var)) [Free f Var]
getInstantiationMappings pos goal = do {res <- getInstantiationMappings' pos goal; traceM (text "getInstantiationMappings" <+> pPrint goal <+> pPrint pos <+> equals <+> pPrint res); return res}
getInstantiationMappings' pos goal = do
    max_d <- getMaxDepth
    kk    <- Map.keys <$> getDB
    let kk_matching_by_c = [ (the c, tt) | (c@(Pred p _ :- _), tt) <- kk, Just (InId <$> p) == rootSymbol goal, then group by c]
    pats <- runListT $ do
        (c, all_tt) <- ListT $ return kk_matching_by_c
        tt <- ListT $ return $
              if P.any isLabelledDown (directSubterms goal)
                      then filter (P.any isLabelledDown . foldMap subterms) all_tt
                      else take 1 (filter (all (not.isLabelledDown) . foldMap subterms) all_tt)
        p_rules    <- lift $ getFresh =<< lookupDB (c,tt)
        let in_r    = inRule p_rules

        -- Check that either we are pattern matching on the rightly labelled constructor or
        -- it is below the maximum depth
        guard ((getId =<< (lhs in_r !* init pos)) == (getId =<< (goal !* init pos))
                || termDepth (lhs in_r) > max_d)

        sigma <- maybe (fail "unify") return (goal `unify` lhs in_r)
      -- check that the patterns contain the labelled constructor
        r          <- ListT $ return $ outRules p_rules
        return (applySubst sigma $ rhs r)
    case pats of
      [] -> do pats' <- nubBy equiv2 <$> deriveRulesForCall pos goal
               assert (not$ null pats') (return ())
               return (Set.fromList  pats')
      _  -> return (Set.fromList (nubBy equiv2 pats))


-- Insert needed rules to compute the success pattern of a given call
deriveRulesForCall pos@(viewLast -> (prefix,i)) call = do
  traceM (text "deriveRulesForCall" <+> pPrint call <+> pPrint pos)
  max_d <- getMaxDepth
  liftM concat $ runListT $ do
--  let rr' = [(k', p++p')
   (k@(c,tt), p_rr) <- ListT (Map.toList <$> getDB)
   let l_in :-> r_in = inRule p_rr
   tt' <- zipWithM copyLabelling tt (mapTermSymbols (fromJust . removePrologId) <$> directSubterms call)

   guard (termDepth l_in <= max_d)
   (v,p') <- l_in !? prefix
   l_in'  <- copyLabelling l_in call
   p_rr'  <- do
        sigma <- maybe (fail "unify") return (l_in' `unify'` call)
--        guard (not (null p'))
        ((c, tt_unlabelled) ,p_rr1) <-
            lift $ instantiatePM (resetLabels <$> sigma) (c, tt') p_rr{inRule = l_in' :-> r_in}

        let tt_labelled = applySubst ( (mapTermSymbols (fromJust.removePrologId)) <$> sigma) <$> tt'
            tt'' = [ if i /= head pos then t else tt_labelled !! (i-1)
                    | (i,t) <- zip [1..] tt_unlabelled]

            p_rr' = let p = take 1 pos in
                    p_rr1{inRule = left(updateAt p (const(applySubst sigma (l_in' ! p)))) (inRule p_rr1)}

            k' =  (c,tt'')

        lift $ appendRR k' p_rr'
{-
      when (isVar v) $ do
             (pos2, rule2) <- do
                           rule2       <- li $ rules p_rr
                           Note (p,v') <- ListT (vars <$> return (annotateWithPosV $ rhs rule2))
                           let Just f = rootSymbol(rhs rule2)
                           guard (not (isUId f) || head p == 1)
                           guard(return v' == v)
                           return (p++p'++[i], rule2)

             lift$ pprTrace (text "deriveRulesForCall" <+> pPrint call <+> text "-->" <+> text "fixOutputPatterns" <+> pPrint (applySubst sigma $ rhs rule2)) $
                   fixOutputPatterns k' pos2 (applySubst sigma $ rhs rule2)
-}
        return p_rr'

   p_rr'' <- lift $ getFresh p_rr'
   let Just sigmaCall = unify (lhs $ inRule p_rr'') call
   return ((applySubst sigmaCall . rhs) <$> outRules p_rr'')

  where li = ListT . return

-- Insert needed rules to handle a new given success pattern
deriveCallsForOutput k out pos = do
  traceM (text "deriveCallsForOutput" <+> pPrint out <+> parens (text "depth:" <+> int(termDepth out))  <+>text "at" <+> pPrint pos)
  max_d <- getMaxDepth
  when (termDepth out <= max_d) $ ignore $ runListT $ do
     l_in <- lift $ (lhs.inRule) <$> lookupDB k
     (k', p_rr) <- ListT (Map.toList <$> getDB)
     r_call    <- li $ callRules p_rr
     guard (Narradar.unifies' l_in (rhs r_call ! [1]))
     let Just uid = rootSymbol (rhs r_call)
         Just u_i = getUId uid

     l:->r     <- li $ getURules uid p_rr
     (v, p')   <- l !? (1 : pos)
     guard (p' /= [])
     sigma     <- unifyPM (l ! [1]) out

     (pos2, rule2) <- do
                      rule2       <- li $ rules p_rr
                      Note (p,v') <- ListT (vars <$> return (annotateWithPosV $ rhs rule2))
                      let Just f = rootSymbol(rhs rule2)
                      guard (case getUId f of
                               Just u_j -> u_j > u_i && head p == 1
                               otherwise-> True)
                      guard(return v' == v)
                      return (p++p', rule2)

     case applySubst sigma $ rhs rule2 of
       r2 | Just (unlabel -> OutId{}) <- rootSymbol r2
          -> lift $ deriveCallsForOutput k' r2 pos2

       r2 -> ignore $ lift $ getInstantiationMappings (tail pos2) (r2 ! [1])
--       ignore :: m a -> m ()

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

amatch pat (isNotvar -> True) = if (isVar .|. isConstant) pat then return pat
                                 else error(show (text "the analysis is not precise enough (notvar):" <+> pPrint pat))
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
-}

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
   trace (show ( -- text "Bddbddb produced the following patterns:" $$ vcat (map pPrint $ concat successpats) $$
                      text "Meaningful pats are: " <> pPrint meaningfulPats)) $ return ()
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
fixSymbols' :: Ord v => NTRS (PrologId (Expr (T (Labelled String) :+: P))) v -> NTRS LRP v
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
-}
-- ---------------------
-- the PrologM monad
-- ---------------------
type PrologKey' id v = (Prolog.Clause'' (WithoutPrologId id) (TermN (WithoutPrologId id) v), [TermN (WithoutPrologId id) v])
type PrologKeyModulo' id v =
    (Prolog.Clause'' (WithoutPrologId id) (TermN (WithoutPrologId id) v), EqModulo [TermN (WithoutPrologId id) v])
type PrologRules' id v = Map (PrologKey' id v)
                             (ClauseRules (RuleN id v))

data PrologMState id v = PrologMState { prologM_kk  :: UniqueList(PrologKeyModulo' id v)
                                      , prologM_af  :: AF_ id
                                      , prologM_sig :: Signature id
                                      , prologM_db  :: PrologRules' id v
                                      , prologM_maxdepth   :: Int
                                      , prologM_u          :: Int
                                      , prologM_staticVars :: Set v
                                      }
--   deriving (Eq, Ord)

prologM_rr st = Map.filterWithKey (\k _ -> k `Set.member` kk) (prologM_db st)
  where kk = Set.fromList [(c, tt) | (c, EqModulo tt) <- UList.toList (prologM_kk st)]

newtype Max a = Max {getMax::a} deriving (Eq,Ord,Bounded,Read,Show,Enum)
instance Monoid (Max Int) where mempty = Max 0; mappend (Max i) (Max j) = Max(max i j)

prologMState db af = PrologMState (UList.fromUniqueList (second EqModulo <$> kk0)) af0 sig0 db (max_depth+1) max_u s_vars
  where
    kk0    = filter (\(Pred p _ :-_,_) -> (InId <$> p) `Set.member` AF.domain af)
                    (Map.keys db)
    rr0    = Map.elems $ Map.filterWithKey (\k _ -> k `Set.member` Set.fromList kk0) db
    sig0   = getSignature db
    af0    = af
             `mappend` AF.init sig0
             `mappend` AF.fromList [ (f,l) | f@(Labelling l _) <- Set.toList $ getConstructorSymbols sig0]

    s_vars = getVars ((lhs.inRule) <$>  rr0)

  -- The maximum depth is determined by the lhs's only or also by terms in the rhs's ?
--    max_depth = Prelude.pred $ getMax $ foldMap3 (Max . termDepth) rr
    max_depth = P.pred $ getMax $ foldMap2 (Max . termDepth) (lhs <$$> db)
    max_u = maximum (0 : [i | id     <- toList (getDefinedSymbols sig0),
                              Just i <- [getUId id]])

--newtype PrologM id v a = PrologM {unPrologM:: StateT (PrologMState id v) (StateT [v]  (AsMonad Set)) a}
newtype PrologM id v a = PrologM {unPrologM:: RWST String [String] (PrologMState id v) (StateT [v] Identity) a}
  deriving (Functor, Monad, MonadFresh v, MonadWriter [String])

--evalPrologM (PrologM m) st0 = m `evalRWST` st0 `evalStateT` ([toEnum 0..] \\ Set.toList(getVars $ prologM_rr st0))
execPrologM (PrologM m) st0 = trace ("running PrologM with max depth " ++ show (prologM_maxdepth st0)) $
                              m `execWST` st0 `evalStateT` ([toEnum 0..] \\ Set.toList(getVars $ prologM_rr st0))
     where execWST m = execRWST m ""

getSt = PrologM get
putSt = PrologM . put

getTheAF :: PrologM id v (AF_ id)

getRR       = prologM_rr  <$> getSt
getTheAF    = prologM_af  <$> getSt
getSig      = prologM_sig <$> getSt
getKK       = prologM_kk  <$> getSt
getDB       = prologM_db  <$> getSt
getMaxDepth = prologM_maxdepth <$> getSt
getUCounter = prologM_u   <$> getSt
getClauses  = (UList.toList . prologM_kk) <$> getSt

modifyKK      f = do {st <- getSt; putSt st{prologM_kk = f (prologM_kk st)}}
modifyDB      f = modifyDB' (Map.mapWithKey f)
modifyDB_at k f = normalizeK k >>= \k' -> modifyDB' (Map.adjust f k)

modifyDB' f = do
  st<- getSt
  let db' = f(prologM_db st)
  putSt st{prologM_db = db'}

modifyAF      f = do {st<- getSt; putSt st{prologM_af  = f (prologM_af st)}}
modifySig     f = do {st<- getSt; putSt st{prologM_sig = f (prologM_sig st)}}
addUCounter   n = do {st<- getSt; putSt st{prologM_u   = prologM_u st + n}}

--putRR new_rr = modifyRR' (const new_rr)
putDepth d   = do {st<-getSt; putSt st{prologM_maxdepth = d }}

appendRR :: PrologKey' LRP Narradar.Var -> ClauseRules (RuleN LRP Narradar.Var) -> PrologM LRP Narradar.Var ()
appendRR k rr = do -- traceUpdatesM Ppr.empty $ do
  kk <- getKK
  k' <- normalizeK k
--  let k'' = second EqModulo k'
--  when (not $ k `UList.elem` kk) $ do
  appendDB k' rr
  modifyKK (UList.cons (second EqModulo k'))

appendDB k rr= normalizeK k >>= \k' -> modifyDB' (Map.insert k' rr)

normalizeK (c,tt) = do
  kk <- Map.keys <$> getDB
  case find (== (c, EqModulo tt)) (second EqModulo <$> kk) of
    Nothing                -> return (c,tt)
    Just (_, EqModulo tt') -> return (c, tt')

mapRR f      = do {rr <- getRR; return (Map.map f rr)}

applyAF :: (AF.ApplyAF t, Ord id, AFId t ~ id) => t -> PrologM id v t
applyAF t    = do {af <- getTheAF; return (AF.apply af t)}

cutAF f i    = modifyAF (AF.cut f i)
extendAF af' = modifyAF (`mappend` af')
updateSignature = do {rr <- getDB; modifySig (const $ getSignature rr); getSig}

lookupClause k = do
  rr <- getRR
  k' <- normalizeK k
  case Map.lookup k' rr of
    Just x -> return x
    Nothing -> error ("lookupClause: " ++ showPpr k)

lookupDB k = do
  rr <- getDB
  k' <- normalizeK k
  case Map.lookup k' rr of
    Just x -> return x
    Nothing -> error ("lookupDB: ") -- ++ showPpr k)

traceM :: Doc -> PrologM id v ()
traceM msg = tell [render msg]

traceUpdatesM :: Doc -> PrologM LRP Narradar.Var a -> PrologM LRP Narradar.Var a
traceUpdatesM tit m = do
   rr  <- getRR
   traceM tit
   res <-  m
   rr' <- getRR
   let common  = List.intersect (rules rr') (rules rr)
       added   = rules rr' \\ common
       deleted = rules rr  \\ common
   when (not (null added && null deleted)) $ do
     db  <- getDB
     traceM (vcat ([text "+" <+> pPrint r <+> parens (pPrint k)
                      | ((Pred p _ :- _, tt), p_rr) <- Map.toList db
                      , let k = Pred p tt
                      , r <- rules p_rr
                      , r `elem` added ]
                 ++ [text "-" <+> pPrint r <+> parens (pPrint k)
                      | ((Pred p _ :- _, tt), p_rr) <- Map.toList db
                      , let k = Pred p tt
                      , r <- rules p_rr
                      , r `elem` deleted ]))
   return res

unifyPM t v = do {v' <- getFresh v; maybe (fail "unify") return (unify t v')}

instantiatePM sigma (c,tt) cc = do
  u <- getUCounter

  let k'  = (c, applySubst (mapTermSymbols (fromJust.removePrologId) <$> sigma) <$> tt)
      cc' = ( applySubst sigma
            . mapRootSymbol (\id -> case mapUId (+u) id of
                                           Just id' -> id'
                                           _        -> id))
            <$$> cc

      new_us = Map.filterWithKey (\k _ -> isUId k) (definedSymbols $ getSignature cc')

  modifySig (\sig -> sig{definedSymbols = definedSymbols sig `mappend` new_us})
  extendAF  (AF.fromList [ (f, [1..a]) | (f,a) <- Map.toList new_us])
  addUCounter (Map.size new_us)
  return (k', cc')

-- -----------------------
-- Built-ins and undefined
--------------------------

Right preludePl = $(do pgm <- runIO (readFile "prelude.pl")
                       case parse Prolog.program "prelude.pl" pgm of -- parse just for compile time checking
                         Left err  -> error (show err)
                         Right _ -> [| fromRight <$$> parse Prolog.program "prelude.pl" pgm |]
                   )                 -- actual parsing ^^ happens (again) at run time.
                                     -- I am too lazy to write the required LiftTH instances.

preludePreds = Set.fromList [ f | Pred f _ :- _ <- preludePl]

--addMissingPredicates :: Program String -> Program String
addMissingPredicates cc0
  | Set.null undefined_cc0 = (insertIs . insertEqual) cc0
  | otherwise              = (insertDummy . insertIs . insertEqual . insertPrelude) cc0

   where undefined_cc0 = undefinedPreds cc0

         undefinedPreds    cc = Set.fromList [ f | f <- Set.toList (getDefinedSymbols cc `Set.difference` definedPredicates cc)]
         definedPredicates :: Program String -> Set String
         definedPredicates cc = Set.fromList [ f | Pred f _ :- _ <- cc]

         insertEqual       cc = if getAny $ foldMap2 (Any . isEqual) cc then eqclause `mappend` cc else cc
         insertIs          cc = if getAny $ foldMap2 (Any . isIs)    cc then isclause `mappend` cc else cc

         eqclause = let x = return (toEnum 1) in [x :=: x :- []]
         isclause = let x = return (toEnum 1) in [Is x x :- []]
         isEqual (_ :=: _) = True; isEqual _ = False
         isIs Is{} = True; isIs _ = False

         insertPrelude cc = if not (Set.null (Set.intersection (undefinedPreds cc) preludePreds)) then cc' `mappend` cc else cc
           where cc' = P.foldr renamePred (cc `mappend` preludePl) (toList repeatedIdentifiers)
                 repeatedIdentifiers = preludePreds `Set.intersection` definedPredicates cc0
         insertDummy cc =  [ Pred f (take (getArity cc f) vars) :- [] | f <- toList (undefinedPreds cc)] ++ cc
         renamePred f = fmap2 (rename (findFreeSymbol cc0 f))
           where rename f' (Pred f tt) | f == f' = Pred f' tt
                 rename _ x = x

         vars = [Prolog.var ("X" ++ show i) | i <- [0..]]

findFreeSymbol sig pre = fromJust $ find (`Set.notMember` getAllSymbols sig) (pre : [pre ++ show i | i <- [0..]])

-- ----------
-- Auxiliary
-- ----------
isLabelledDown t = fromMaybe False $ liftA2 (<) (length <$> (getLabel =<< rootSymbol t)) (Just $ length (directSubterms t))

resetLabels = foldTerm return f where
  f t = Impure $ mapId (mapLabel (\_ -> Just [1 .. length (Data.Foldable.toList t)])) t

viewLast pos = (init pos, last pos)

iFun sig f = [1.. getArity sig f]

isConstant = null . directSubterms

--fixSymbols :: (Ord a, Ord v) => PrologRules (PrologId (Labelled a)) v -> PrologRules (Labelled (PrologId a)) v
fixSymbols = (Map.map . fmap) (fmap (mapTermSymbols fixLabelling))

fixLabelling :: Ord a => PrologId (Labelled a) -> Labelled (PrologId a)
fixLabelling t = case toList t of  -- hack to get to the id inside the PrologId
                  [Plain     _]   -> Plain       pt
                  [Labelling l t] -> Labelling l pt
                  [] {- so UId -} -> Plain pt
     where [lt] = toList t
           pt   = fmap unlabel t

--copyLabelling :: (HasId t id, IsLabelled id, Eq (t ()), Traversable t, MapId f, t ~ f id) => Term t v -> Term t v -> Term t v
-- | @copyLabelling t u@ returns @t@ with the labelling of @u@ if the structure of @t@ and @u@ matches
--copyLabelling t u | pprTrace (text "copyLabelling" <+> pPrint t <+> pPrint u) False = undefined
copyLabelling t u = f t u where
  f t@(Impure tf) u@(Impure uf) = do
           when (fmap (const ()) (mapId unlabel tf) /= fmap (const ()) (mapId unlabel uf)) $
                fail "copyLabelling : structure mismatch"
           let tf' = mapId (mapLabel (const (getLabel =<< getId uf))) tf
           Impure <$> unsafeZipWithGM f tf' uf
  f t _ = return t

termDepth = foldTerm (const 0) f where
--    f Wildcard = 0
    f tf = 1 + F.maximum (0 : toList tf)

traceUpdates tit rr rr' =
    pprTrace (tit $$
              vcat ([text "+" <+> pPrint r | r <- toList added]
                 ++ [text "-" <+> pPrint r | r <- toList deleted])) rr'
  where
    common  = List.intersect (rules rr') (rules rr)
    added   = rules rr' \\ common
    deleted = rules rr  \\ common

-- ------------------
-- Functor Instances
-- ------------------

$(derive makeFunctor     ''ClauseRules)
$(derive makeFoldable    ''ClauseRules)
$(derive makeTraversable ''ClauseRules)
