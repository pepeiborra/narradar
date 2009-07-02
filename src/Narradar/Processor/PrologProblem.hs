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
import Control.Arrow
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
import Data.Foldable    (Foldable, toList, notElem)
import Data.Traversable (Traversable)
import qualified  Data.Traversable as T
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Haskell.TH (runIO)
import Text.ParserCombinators.Parsec (parse)
import Text.PrettyPrint hiding (Mode(..))
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

-- ----------------
-- Transformations
-- ----------------

type PrologRules id v = Map (WithoutPrologId id) (Set (RuleN id v))

skTransform :: (Ord id, Ord v, Ppr id) =>
                [Prolog.Clause'' id (TermN id v)] -> PrologRules (PrologId id) v
skTransform clauses = Map.fromListWith mappend clauseRules where

       clauseRules = runSupply (mapM (runClause . toRule . fmap2 (mapTermSymbols FunctorId)) clauses)

         -- The counter for u_i is global,
         -- the list of vars is local to each clause.
       runClause = (`evalStateT` mempty)

       toRule (Pred id tt :- (filter (/= Cut) -> [])) = do
         return (id, Set.singleton (term (InId id) tt :-> term (OutId id) tt))

       toRule (Pred id tt :- (filter (/= Cut) -> gg)) = do
         modify (getVars tt `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (InId id) tt :-> rhs_0
             r_n = lhs_n :-> term (OutId id) tt
         return (id, Set.fromList (r_0 : r_n : mid_r))

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
                         Right _ -> [| fromRight <$$> parse Prolog.program "prelude.pl" pgm|]
                   )                 -- actual parsing ^^ happens (again) at run time.
                                     -- I am too lazy to write the required LiftTH instances.


preludePreds = Set.fromList [ f | Pred f _ :- _ <- preludePl]
addMissingPredicates cc0
  | Set.null undefined_cc0 = cc0
  | otherwise = (insertDummy . insertEqual . insertPrelude) cc0

   where undefined_cc0 = undefinedPreds cc0
         vars = [Prolog.var ("X" ++ show i) | i <- [0..]]
         undefinedPreds    cc = Set.fromList [ f | f <- toList (getDefinedSymbols cc `Set.difference` definedPredicates cc)]
         definedPredicates cc = Set.fromList [ f | Pred f _ :- _ <- cc]
         insertEqual       cc = if getAny $ foldMap2 (Any . isEqual) cc then eqclause `mappend` cc else cc
           where eqclause = let x = Prolog.var "X" in [x :=: x :- []]
                 isEqual (Is _ _ ) = True; isEqual (_ :=: _) = True; isEqual _ = False
         insertPrelude cc = if not (Set.null (Set.intersection (undefinedPreds cc) preludePreds)) then cc' `mappend` cc else cc
           where cc' = foldr renamePred (cc `mappend` preludePl) (toList repeatedIdentifiers)
                 repeatedIdentifiers = preludePreds `Set.intersection` definedPredicates cc0
         insertDummy cc =  [ Pred f (take (getArity cc f) vars) :- [] | f <- toList (undefinedPreds cc)] ++ cc
         renamePred f = fmap2 (rename (findFreeSymbol cc0 f))
           where rename f' (Pred f tt) | f == f' = Pred f' tt
                 rename _ x = x


findFreeSymbol sig pre = fromJust $ find (`Set.notMember` getAllSymbols sig) (pre : [pre ++ show i | i <- [0..]])


labellingPredsTrans :: forall heu v.
                       (PolyHeuristicN heu LRP, v ~ Narradar.Var) =>
                          MkHeu heu -> AF_ String -> Prolog.Program String
                       -> Set(PrologRules LRP v, AF_ LRP, Signature LRP)
--labellingPredsTrans _   _      []  = Set.singleton mempty
labellingPredsTrans mkH goalAF pgm = unEmbed $ do

    let af0  = AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList skgoal] `mappend` AF.init sig0
        sig0 = getSignature rr0

        rr0  = mconcat [insertNewMode f pp | (InId f, pp) <- AF.toList skgoal]

    (rr1, af1, sig1) <- invariantEV (rr0, af0, sig0)

    -- ("Rules added:\n" ++ unlines (map show $ Types.rules added) ) $
--    trace (unlines(map showPpr $ rules rr0) ++ "\n" ++ showPpr af0) $ return ()

    fix invariantNewModes (rr1, af1, sig1)

 where
  heuristic = mkHeu mkH (prologTRS' lrr)

  skrr   = skTransform (prepareProgram $ addMissingPredicates pgm)
  skgoal = skTransformAF pgm goalAF
  sksig  = getSignature skrr

  lrr = Map.fromListWith mappend [ (Labelling (iFun sksig (InId k)) k, (Set.mapMonotonic . fmap) (labelTerm (not.isFunctorId)) rr)
                           | (k,rr) <- Map.toList skrr]

  invariantNewModes f (the_m, af, _)
      | Set.null new_modes = return (the_m, af, sig0)
      | otherwise          = f =<< invariantEV =<< foldM g (the_m, af, sig0) (Set.toList new_modes)
     where
          sig0      = getSignature the_m
          new_modes =  Set.fromList [ Labelling l s | (Labelling l (InId s)) <- Set.toList (allSymbols sig0)]
                      `Set.difference` Map.keysSet the_m
          g prev@(rr0, af, sig) (Labelling pp id) = (prev `mappend`) `liftM` invariantEV (rr', af', sig')
            where
              rr'  = insertNewMode id pp
              sig' = getSignature (rr' `mappend` rr0)
              af'  = af `mappend` AF.init sig'

  invariantEV (the_m, af, sig)
      | ((rr_pred,pred,rule,pos):_) <- extra
      = cutEV rule pos pred sig rr_pred af >>= \(rr',af',sig') -> invariantEV (Map.insert pred rr' the_m, af', sig')
      | otherwise  = return (the_m, af, sig)
      where extra = [(rr, pred, r, noteV (head ev))
                             | (pred,rr) <- Map.toList the_m, r <- Set.toList rr
                             , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
                             , not (null ev)]

  insertNewMode id pp | trace ("\ninsertNewMode " ++ showPpr (id,pp)) False = undefined
  insertNewMode id pp =
    let lid = Labelling (iFun sksig (InId id)) id
    in (Map.singleton (Labelling pp id) $
               Set.fromList [l `setLabel` Just pp :-> r `setLabel` Just pp
                                 | (l :-> r) <- maybe (error "labellingPredTrans.insertNewMode")
                                                      toList
                                                      (Map.lookup lid lrr)])

  cutEV rule@(l:->r) pos pred sig rr af = do
      (f, i) <- embed $ runHeu heuristic af r pos
      trace ("pred: " ++ showPpr pred ++ ", symbol:" ++ showPpr f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ showPpr (AF.apply af rule)) $ return ()
      case f of
        Labelling _lab (InId f_pred) -> do
         let (Impure (Term u@(unlabel -> UId{}) (Impure (Term g@(Labelling lab (InId gid)) vv2) : vv1))) = r
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
         let rr' = (changes1 . changes3) rr
             af' = af `mappend` AF.fromList [(gl_in, labelling gl'), (gl_out, [1..g_arity])]
             sig'= sig{definedSymbols = definedSymbols sig `mappend` Set.fromList [gl_in, gl_out],
                       arity = arity sig `mappend` Map.fromList [(gl_in, g_arity), (gl_out, g_arity)]}

             common = Set.intersection rr' rr; added = rr' `Set.difference` common; deleted = rr `Set.difference` common
         trace ("\nAdded " ++ show (Set.size added) ++ " rules and deleted " ++ show (Set.size deleted) ++"\n" ++
                "Rules added:\n" ++ unlines (map showPpr $ toList added) ++"\nRules deleted:\n" ++ unlines (map showPpr $ toList deleted) ++
                "\nResulting Rules and AF:\n" ++ unlines(map showPpr $ toList rr') ++ "\n" ++ showPpr af') $ return ()

         return (rr', af', sig')

        _ -> return (rr, AF.cut f i af, sig)

-- labellingPredsTrans _ af p = R.return ((convert p, convert af), [])



type P'   = Abstract :+: V :+: PF
type LP'  = Labelled (Expr (Abstract :+: V :+: PF))
type Pred = NotAny   :+: V :+: PF

labellingConsTrans :: forall m v. (v ~ Narradar.Var) =>
                      [FilePath] -> (String, [Mode]) -> [Clause String]
                   -> Set((PrologRules LRP v, AF_ LRP), Set LRP)
--labellingConsTrans  _ [] = return (Set.singleton mempty)
--labellingConsTrans (g,_)  pgm | g `Set.notMember` getDefinedSymbols pgm = error "labellingConsTrans: not a valid goal"
labellingConsTrans bddbddb_path (g,mm) pgm = runIt $ do
   let abstractGoal  = abstractCompileGoal g [ m == G | m <- mm]

       cs_opts :: ComputeSuccessPatternsOpts Pred (T String :+: P')
       cs_opts = computeSuccessPatternsOpts{ pl = pgm
                                           , mb_goal = Just abstractGoal
                                           , depth = 1
                                           , bddbddb_path
#ifdef DEBUG
                                           , verbosity = 1
#endif
                                           }

       (_dom, successpats) = unsafePerformIO $ computeSuccessPatterns cs_opts

       filteredPats = [ (p, evalTerm (const any) (\(T x) -> x) <$> tt)
                          | Pred (Al.match -> Just (Answer p)) tt <- concat successpats
--                          , let tt' =  [ pat | Impure (T pat) <- tt, not (isNotvar pat), not (isAny pat)]
                          , let special = [ () | Impure (T (Al.match -> Just(Compound _ ss))) <- tt
                                               , s <- ss
                                               , isAny s]
                          , not (null special)
                          ]

       additionalClauses = concatMap mkClauses filteredPats

       pl'  = prepareProgram (addMissingPredicates pgm)
       lpgm = mapTermSymbols (\c -> Labelling (iFun pl' c) c) <$$$> (mapPredId Plain <$$> pl')
       rr0  = fixSymbols $ skTransform (additionalClauses ++ lpgm)
       af0  = AF.mapSymbols Plain (skTransformAF pgm (mkGoalAF (g,mm))) `mappend` AF.init rr0

#ifdef DEBUG
   trace (show (  text "Bddbddb produced the following patterns:"  $$ vcat (map ppr $ concat successpats) $$
                  text "Meaningful pats are: " <> ppr filteredPats $$
                  text "Added the clauses:" $$ (vcat (map ppr additionalClauses)))) $ return ()
#endif

   fix invariantEV (rr0, af0)

 where
  runIt = unEmbed . runWriterT

  rep_pgm = prepareProgram pgm
  sig_pl  = getSignature $ toList3 rep_pgm -- Only the constructors

  mkClauses (p, apats) = clauses where
    clauses= [ Pred (Plain p') pats' :- fmap (mapPredId Plain) gg
                         | (Pred p' pats :- gg) <- fmap3 (mapTermSymbols Plain) rep_pgm
                         , reinject p' == p
                         , Just pats' <- [zipWithM amatch pats apats]]

  invariantEV f (the_m, af)
      | ((pred,rule,pos):_) <- extra = cutEV pred rule pos (the_m,af) >>= f
      | otherwise  = return (the_m, af)
      where extra = [(pred, r, noteV (head ev))
                             | (pred, rr) <- Map.toList the_m
                             , r <- Set.toList rr
                             , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
                             , not (null ev)]
  cutEV pred rule@(l:->r) pos (rr, af) = do
      let i      = last pos
          Just f = rootSymbol (r ! init pos)
      trace ("pred: " ++ showPpr pred ++ ", symbol:" ++ showPpr f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ showPpr (AF.apply af rule)) $ return ()
      case f of
        Labelling lab (FunctorId f_l) -> do
          let f_l' = Labelling (delete i lab) f_l
              f'   = FunctorId <$> f_l'
              r'   = updateAt (init pos) r (mapRootSymbol (const f'))
              rr'  = Map.insertWith (\x rr0 -> Set.union x $ Set.delete rule rr0)
                                            pred (Set.singleton (l :-> r')) rr
              af'  = af `mappend` AF.singleton f' (labelling f_l')

          tell (Set.singleton f')

          R.return (rr', af')

        _ -> R.return (rr, AF.cut f i af)


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

{-| Abstract matching
    Takes a labelled pattern and an abstract value and restricts the
    labellings in the pattern according to the abstract value.
    It does understand multi-level patterns and abstract values.

    > amatch [_|_] static = [_|_]
    > amatch [_|_] [s|a]  = [_|_]_1
    > amatch [_|_] [a|s]  = [_|_]_2
-}
amatch :: (t ~ termF lid, lid ~ (Labelled(Expr f')), MapId termF, Traversable t, HasId t lid, Eq (Expr f),
               Compound :<: f, NotVar :<: f, Prolog.Any :<: f, f' :<: f, MonadPlus m) =>
              Free t v -> Expr f -> m (Free t v)

amatch pat (isNotvar -> True) = return pat
amatch pat (isAny    -> True)
  | isVar pat = return pat
  | otherwise = mzero

amatch pat@(fmap unlabel . getId -> Just c) apat@(Al.match -> Just (Compound c' tt'))
-- > amatch [:pterm| c tt] [:oexpr| c' tt'] =
   = do
        guard (reinject c == c' && length (directSubterms pat) == length tt')
        let ll = [ i | (i,a) <- (zip [1..] tt'), not (isAny a)]
        let pat1 = mapRootSymbol (\_->Labelling ll c) pat
        pat' <- evalTerm return2 (\tt -> liftM Impure $ unsafeZipWithGM (flip amatch) tt' tt) pat1
        return pat'
amatch _ _ = fail "amatch: patterns didn't match"


fixSymbols :: (Ord a, Ord v) => PrologRules (PrologId (Labelled a)) v -> PrologRules (Labelled (PrologId a)) v
fixSymbols = (Map.map . Set.map) (fmap (mapTermSymbols fixLabelling))

fixLabelling :: Ord a => PrologId (Labelled a) -> Labelled (PrologId a)
fixLabelling t = case toList t of  -- hack to get to the id inside the PrologId
                  [Plain     _]   -> Plain       pt
                  [Labelling l t] -> Labelling l pt
                  [] {- so UId -} -> Plain pt
     where [lt] = toList t
           pt   = fmap unlabel t

-- ----------
-- Auxiliary
-- ----------

iFun sig f = [1.. getArity sig f]
