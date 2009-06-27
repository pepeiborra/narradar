{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
                                          computeSuccessPatternsOpts, DatalogTerm)
import qualified Language.Prolog.Representation as Prolog
import Language.Prolog.Representation (representTerm, representProgram,
                                       Term0, term0, T(..), PrologT, PrologP, V, NotVar, Compound(..),
                                       cons, nil, psucc, zero, tup, eq, is,
                                       any, notvar, compound, mkT,
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

type P    = PrologT :+: PrologP :+: T String
type PS   = PrologId (Expr P)
type PId  = Identifier PS
type LPS  = Labelled PS
type LPId = Identifier LPS

type LPS' = PrologId (Labelled (Expr P))
type LPId'= Identifier LPS'

instance Convert PS     LPId      where convert = IdFunction . Plain
instance Convert PId    LPId      where convert = fmap Plain
instance Convert PS   PS   where convert = id
instance Convert PId  PId  where convert = id
instance Convert LPS  LPS  where convert = id
instance Convert LPId LPId where convert = id

-- ---------
-- Analysis
-- ---------
inferType (Problem Prolog{program} _ _) = infer program


-- --------------
-- Processors
-- --------------

prologP_sk :: (PolyHeuristicN heu PId, MonadPlus m, MonadFree ProofF m) =>
              MkHeu heu -> PrologProblem Narradar.Var -> m (Problem PId Narradar.Var)
prologP_sk heu p0@(Problem Prolog{..} _ _) =
   andP PrologSKP p0
     [ msum (map return pp)
         | let sk_p          = skTransform (prepareProgram $ addMissingPredicates program)
         , goal0            <- goals
         , let goal          = skTransformAF program goal0
               af_groundinfo = AF.init sk_p `mappend` goal
               pp            = mkGoalProblem heu GNarrowingModes{goal, pi=af_groundinfo} sk_p
     ]


prologP_labelling_sk :: (PolyHeuristicN heu LPS, PolyHeuristicN heu LPId, MonadFree ProofF m, v ~ Narradar.Var) =>
                        MkHeu heu -> PrologProblem v -> m (Problem LPId v)
prologP_labelling_sk mkHeu p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingSKP []) p0
  | otherwise  = mall problems
  where problems = do
                       goal <-goals
                       let goal_lps = AF.mapSymbols' (flip Labelling) (skTransformAF program goal)
                       ((trs, pi), modes) <- toList $ labellingPredsTrans mkHeu goal program
                       let pp' = mkGoalProblem mkHeu GNarrowingModes{pi, goal = goal_lps} trs
                       return $ orP (LabellingSKP modes) p0 (map return pp')


prologP_labelling_cons :: (MonadFree ProofF m, v ~ Narradar.Var) =>
                        PrologProblem v -> m (Problem LPId' v)
prologP_labelling_cons p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingCP []) p0
  | otherwise  = mall problems
  where problems = do
                       g      <- goals
                       (f,ii) <- AF.toList g
                       let query = (f, [ if i `elem` ii then G else V | i <- [1..getArity program f]])
                           goal  = AF.mapSymbols (Plain <$>) (skTransformAF program g)
                       ((trs, pi), modes) <- toList $ runReader (labellingConsTrans query program)
                                                         ["/Users/pepe/Downloads/bddbddb-full.jar"]
                       let pp'     = mkGoalProblem (simpleHeu innermost) GNarrowingModes{pi, goal} trs
                           newCons = [ showPpr <$> c | FunctorId c <- Set.toList $ mconcat (Map.elems modes)]
                       return $ orP (LabellingCP newCons) p0 (map return pp')

-- ----------------
-- Transformations
-- ----------------

skTransform :: (Ord id, Ord v, Ppr id) =>
                [Prolog.Clause'' id (TermN id v)] -> NarradarTRS (PrologId id) v
skTransform clauses = prologTRS clauseRules where

       clauseRules = concat $ runSupply (mapM (runClause . toRule . fmap2 (mapTermSymbols FunctorId)) clauses)

         -- The counter for u_i is global,
         -- the list of vars is local to each clause.
       runClause = (`evalStateT` (mempty {-:: Set v -}))

       toRule (Pred id tt :- (filter (/= Cut) -> [])) = do
         return [(showPpr id, term (InId id) tt :-> term (OutId id) tt)]

       toRule (Pred id tt :- (filter (/= Cut) -> gg)) = do
         modify (getVars tt `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (InId id) tt :-> rhs_0
             r_n = lhs_n :-> term (OutId id) tt
         return $ zip (repeat (showPpr id)) (r_0 : r_n : mid_r)

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


skTransformAF sig = AF.mapSymbols (\f -> if f `Set.member` getDefinedSymbols sig
                                         then InId (mkT f)
                                         else FunctorId (mkT f))

prepareProgram :: (PrologP :<: f, PrologT :<: f, T id :<: f) =>
                  Program id -> Program'' (Expr f) (TermN (Expr f) Narradar.Var)
prepareProgram = (`evalState` (mempty {- :: Map String Narradar.Var -})) . (`evalStateT` (toEnum <$> [0..]))
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


labellingPredsTrans :: forall heu v. (PolyHeuristicN heu LPS, v ~ Narradar.Var) =>
                  MkHeu heu -> AF_ String -> Prolog.Program String -> Set((NarradarTRS LPS v, AF_ LPS), [LS])
labellingPredsTrans _   _      []  = Set.singleton mempty
labellingPredsTrans mkH goalAF pgm = unEmbed $ runWriterT $ do

    trs0 <- (prologTRS' . mconcat) `liftM` (
             liftM2 (++) (sequence [insertNewMode (f, pp) | (InId f, pp) <- AF.toList (AF.init sktrs)])
                         (sequence [insertNewMode (f, pp)
                                   | (InId f, pp) <- AF.toList skgoal
                                   , pp /= iFun sktrs (InId f)])
                                           )
    let af0  = AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList skgoal]
               `mappend` AF.init trs0

    -- ("Rules added:\n" ++ unlines (map show $ Types.rules added) ) $
    trace (unlines(map showPpr $ rules trs0) ++ "\n" ++ showPpr af0) $
     fix invariantEV (trs0, af0)
 where
  heuristic = mkHeu mkH trs'

  sktrs@(PrologTRS rr _)  = skTransform (prepareProgram $ addMissingPredicates pgm)
  skgoal = skTransformAF pgm goalAF

  trs' = prologTRS' lrr
  lrr  = Set.map (second (fmap (labelTerm (isInId .|. isOutId)))) rr

--  insertNewMode :: NarradarTRS (Labelled id) f' -> (Labelled id, [Int] -> [Int]) -> NarradarTRS (Labelled id) f'
  insertNewMode (id,pp) | trace ("insertNewMode " ++ showPpr (id,pp)) False = undefined
  insertNewMode (Al.match -> Just (T id), pp) = tell [Labelling pp id] >>
                           return (Set.fromList [ (pred, l `setLabel` Labelling pp :-> r `setLabel` Labelling pp)
                                                 | (pred, l :-> r) <- toList lrr
                                                 ,  pred == id])
  invariantEV f (trs@(PrologTRS rr _), af)
      | ((pred,rule,pos):_) <- extra = cutEV pred rule pos (trs,af) >>= f
      | otherwise  = return (trs, af)
      where extra = [(pred, r, noteV (head ev))
                             | (pred,r) <- toList rr
                             , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
                             , not (null ev)]
  cutEV pred rule@(l:->r) pos (trs@(PrologTRS rr _), af) = do
      (f, i) <- lift $ embed $ runHeu heuristic af r pos
      trace ("pred: " ++ showPpr pred ++ ", symbol:" ++ showPpr f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ showPpr (AF.apply af rule)) $ return ()
      case unlabel f of
        InId f_pred -> do
         let (Impure (Term u@(unlabel -> UId{}) (Impure (Term g@(unlabel -> InId{}) vv2) : vv1))) = r
             f'  = assert (f==g) $ mapLabel (Labelling . delete i) (Labelling (delete i $ iFun trs g)) g
             r' = term u (term f' vv2 : vv1)
             changes1 =  Set.insert (pred, l:->r') . Set.delete (pred,rule)
             changes2 x = if f' `notElem` (getDefinedSymbols trs) then  (mappend x) `liftM`insertNewMode (f_pred, labelling f') else return x
             changes3 = foldr (.) id
                        [ Set.insert (pred',outrule') . Set.delete (pred',outrule)
                                | (pred', outrule@(l :-> r)) <- toList rr
                                , (Impure (Term u' (Impure (Term p_out@(unlabel -> OutId h) vv2) : vv1))) <- [l]
                                , u == u', h == f_pred
                                , let outrule' = term u (term (mapLabel (Labelling . delete i) (Labelling (delete i $ iFun trs p_out))  p_out) vv2 : vv1) :-> r]
         trs'@(PrologTRS rr' _) <- (prologTRS' .changes1 . changes3) `liftM` changes2 rr
         let af' = af `mappend` AF.singleton f' (labelling f') `mappend` AF.init trs'
             common = Set.intersection rr' rr; added = rr' `Set.difference` common; deleted = rr `Set.difference` common
         trace ("Added " ++ show (Set.size added) ++ " rules and deleted " ++ show (Set.size deleted) ++"\n" ++
                "Rules added:\n" ++ unlines (map (showPpr.snd) $ toList added) ++"\nRules deleted:\n" ++ unlines (map (showPpr.snd) $ toList deleted) ++
                "\n" ++ unlines(map (showPpr.snd) $ toList rr') ++ "\n" ++ showPpr af') $ return ()
         R.return (trs', af')
        _ -> R.return (trs, AF.cut f i af)

-- labellingPredsTrans _ af p = R.return ((convert p, convert af), [])



type P'   = V :+: PrologT :+: PrologP :+: Prolog.Any :+: NotVar :+: Compound

labellingConsTrans :: forall m v. (v ~ Narradar.Var, MonadReader [FilePath] m) =>
                      (String, [Mode]) -> [Clause String] -> m(Set((NarradarTRS LPS' v, AF_ LPS'), Map String (Set LPS')))
--labellingConsTrans  _ [] = return (Set.singleton mempty)
--labellingConsTrans (g,_)  pgm | g `Set.notMember` getDefinedSymbols pgm = error "labellingConsTrans: not a valid goal"
labellingConsTrans (g,mm) pgm = ask >>= \bddbddb_path -> return $ runIt $ do

   let abstractGoal :: GoalF String (DatalogTerm (Expr (T String :+: P')))
       abstractGoal  = Prolog.Pred g [ if m == G then term0 notvar else Pure (Right v)
                                          | (v,m) <- zip [toEnum 0..] mm]

       cs_opts :: ComputeSuccessPatternsOpts (T String :+: P')
       cs_opts = computeSuccessPatternsOpts{ pl = pgm
                                           , mb_goal = Just abstractGoal
                                           , depth = 1
                                           , bddbddb_path
#ifdef DEBUG
                                           , verbosity = 2
#endif
                                           }

       (_dom, successpats) = unsafePerformIO $ computeSuccessPatterns cs_opts


       filteredPats = [ (p :: String, evalTerm (error "labellingConsTrans/meaningful pats: the impossible happened ")
                                               (\(T x) -> x) <$> tt)
                          | Pred (Al.match -> Just (Answer p)) tt <- concat successpats `const` abstractGoal
                          , let tt' =  [ pat | Impure (T pat) <- tt, not (isNotvar pat), not (isAny pat)]
                          , not (null tt')
                          ]

       additionalClauses = concatMap mkClauses filteredPats

       lpgm              = mapTermSymbols Plain <$$$> (mapPredId Plain <$$> prepareProgram (addMissingPredicates pgm))
       trs0              = skTransform (additionalClauses ++ lpgm)
       af0               = AF.mapSymbols (fmap Plain) (skTransformAF pgm (mkGoalAF (g,mm))) `mappend` AF.init trs0


   ((res, af), newCons) <- listen $ fix invariantEV (trs0, af0)

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
   return (res, af)
 where
  runIt = Set.mapMonotonic(second(Map.fromListWith mappend)) . unEmbed . runWriterT

  rep_pgm = prepareProgram pgm
  sig_pl  = getSignature $ toList3 rep_pgm -- Only the constructors

  mkClauses (p, apats) = clauses where
    clauses= [ Pred (Plain p') pats' :- fmap (mapPredId Plain) gg
                         | (Pred p'@(Al.match -> Just (T ps)) pats :- gg) <- fmap3 (mapTermSymbols Plain) rep_pgm
                         , ps == p
--                       , and (zipWith amatches pats apats)
                         , Just pats' <- [zipWithM concretize pats apats]]

  invariantEV f (trs@(PrologTRS rr _), af)
      | ((pred,rule,pos):_) <- extra = cutEV pred rule pos (trs,af) >>= f
      | otherwise  = return (trs, af)
      where extra = [(pred, r, noteV (head ev))
                             | (pred,r) <- toList rr
                             , let ev = extraVars (AF.apply af (annotateWithPos `fmap` r))
                             , not (null ev)]
  cutEV pred rule@(l:->r) pos (trs@(PrologTRS rr _), af) = do
      let i      = last pos
          Just f = rootSymbol (r ! init pos)
      trace ("pred: " ++ showPpr pred ++ ", symbol:" ++ showPpr f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ showPpr (AF.apply af rule)) $ return ()
      case f of
        FunctorId f_l -> do
          let f_l' = mapLabel (Labelling . delete i) (Labelling (delete i $ iFun trs f)) f_l
              f'   = FunctorId f_l'
              r'   = updateAt (init pos) r (mapRootSymbol (const f'))
              trs' = prologTRS' $ Set.insert (pred, l :-> r') $ Set.delete (pred,rule) $ rr
              af'  = af `mappend` AF.singleton f' (labelling f_l')

          tell [(pred, Set.singleton f')]

          R.return (trs', af')

        _ -> R.return (trs, AF.cut f i af)

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

fixSymbols' :: Ord v => NarradarTRS (PrologId (Expr (T (Labelled String) :+: P))) v -> NarradarTRS LPS v
fixSymbols' (PrologTRS rr sig) = prologTRS' rr'  where
  rr'         = Set.map (second (fmap (mapTermSymbols fixSymbol))) rr
  fixSymbol t = case runWriter (T.mapM (foldExprM removeLabelF) t) of
                  (t', Nothing) -> Plain t'
                  (t', Just ll) -> Labelling ll t'

fixSymbols :: (Ord a, Ord v) => NarradarTRS (PrologId (Labelled a)) v -> NarradarTRS (Labelled (PrologId a)) v
fixSymbols (PrologTRS rr sig) = prologTRS' rr'
   where rr' = Set.map (second (fmap (mapTermSymbols fixLabelling))) rr

fixLabelling :: Ord a => PrologId (Labelled a) -> Labelled (PrologId a)
fixLabelling t = case toList t of  -- hack to get to the id inside the PrologId
                  [Plain     _]   -> Plain       pt
                  [Labelling l t] -> Labelling l pt
                  [] {- so UId -} -> Plain pt
     where [lt] = toList t
           pt   = fmap unlabel t

class (Functor f, Functor g) => RemoveLabelF f g where removeLabelF :: MonadWriter (Maybe [Int]) m => f (Expr g) -> m(Expr g)
instance (RemoveLabelF f1 g, RemoveLabelF f2 g)  => RemoveLabelF (f1 :+: f2) g where
   removeLabelF (Inl l) = removeLabelF l
   removeLabelF (Inr r) = removeLabelF r
instance (a :<: g) => RemoveLabelF a g where removeLabelF = return . inject . fmap reinject
instance (T id :<: g) => RemoveLabelF (T (Labelled id)) g where
   removeLabelF (T (Labelling ll x)) = tell (Just ll) >> return (mkT x)

{-| Takes a labelled pattern and an abstract value and restricts the
    labellings in the pattern according to the abstract value.
    It does understand multi-level patterns and abstract values.

    > concretize [_|_] static = [_|_]
    > concretize [_|_] [s|a]  = [_|_]_1
    > concretize [_|_] [a|s]  = [_|_]_2
-}


concretize :: (t ~ termF lid, lid ~ (Labelled(Expr f')), MapId termF, Traversable t, HasId t lid, Eq (Expr f),
               Compound :<: f, NotVar :<: f, Prolog.Any :<: f, f' :<: f, MonadPlus m) =>
              Free t v -> Expr f -> m (Free t v)

concretize pat (isNotvar -> True) = return pat
concretize pat (isAny    -> True)
  | isVar pat = return pat
  | otherwise = error ("concretize: Incomplete analysis of success patterns, " ++
                       "the abstract domain is not deep enough")

concretize pat@(fmap unlabel . getId -> Just c) apat@(Al.match -> Just (Compound c' tt'))
-- > concretize [:pterm| c tt] [:oexpr| c' tt'] =
   = do
        guard (reinject c == c' && length (directSubterms pat) == length tt')
        let ll = [ i | (i,a) <- (zip [1..] tt'), not (isAny a)]
        let pat1 = mapRootSymbol (\_->Labelling ll c) pat
        pat' <- evalTerm return2 (\tt -> liftM Impure $ unsafeZipWithGM (flip concretize) tt' tt) pat1
        return pat'
concretize _ _ = fail "concretize: patterns didn't match"


-- ----------
-- Auxiliary
-- ----------
labelTerm :: IsPrologId id => (id -> Bool) -> TermN id v -> TermN (Labelled id) v
labelTerm pred = foldTerm return f where
  f (Term id tt)
    | pred id   = term (Labelling [1..length tt] id) tt
    | otherwise = term (Plain id) tt

iFun sig f = [1.. getArity sig f]
