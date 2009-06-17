{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances, TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}

module Narradar.PrologProblem where -- (inferType, prologP_sk, prologP_labelling_sk, skTransform) where

import Control.Applicative
import Control.Arrow
import Control.Exception (assert)
import Control.Monad.Error (Error)
import Control.Monad.Free.Narradar (foldFreeM)
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Supply
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.Char (isSpace)
import Data.HashTable (hashString)
import Data.List (partition, isSuffixOf, isPrefixOf, delete, (\\), sort, groupBy, find)
import Data.Maybe
import Data.Monoid
import Data.Foldable (toList, notElem)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Language.Haskell.TH (runIO)
import Text.ParserCombinators.Parsec (parse, ParseError, getInput)
import Text.XHtml (Html, toHtml)

import Language.Prolog.Syntax (Clause, ClauseF(..), Program, GoalF(..), Goal,
                               TermF(Cons, Nil, Tuple, Wildcard, String, Int, Float))
import qualified Language.Prolog.Syntax as Prolog
import qualified Language.Prolog.Parser as Prolog (program, clause, query, whiteSpace, ident)
import Language.Prolog.SharingAnalysis (infer)
import Data.Term.Var as Prolog (Var(VName, VAuto))

import Lattice (Lattice)

import Narradar.ArgumentFiltering (AF_, AF, typeHeu, innermost, MkHeu, mkHeu, PolyHeuristicN, Heuristic(..))
import qualified Narradar.ArgumentFiltering as AF
import Narradar.DPairs
import Narradar.Types hiding (Var,Term, program)
import Narradar.Types as Term
import Narradar.NarrowingProblem
import Narradar.Proof
import Narradar.ExtraVars
import Narradar.Utils ((<$$>),(..&..), showPpr, mapLeft, on, fmap2, foldMap2, return2, trace)
import Prelude hiding (and,or,notElem,pi)

inferType (Problem Prolog{..} _ _) = infer program

-- ----------------
-- Transformations
-- ----------------

prologP_sk :: (PolyHeuristicN heu PId, MonadPlus m, MonadFree ProofF m) =>
              MkHeu heu -> PrologProblem Term.Var -> m (ProblemG PId Term.Var)
prologP_sk heu p0@(Problem Prolog{..} _ _) =
   andP PrologSKP p0
     [ msum (map return pp)
         | goal0 <- goals
         , let sk_p          = skTransform program
               goal          = AF.mapSymbols InId goal0
               af_groundinfo = AF.init sk_p ` mappend` goal
               pp            = mkGoalProblem heu (GNarrowingModes goal af_groundinfo) sk_p
     ]

skTransform :: forall v. (v ~ Term.Var) => [Clause String] -> NarradarTRS PS v
skTransform (addMissingPredicates -> clauses) = prologTRS clauseRules where
       sig = getSignature clauses

       [equalF, commaF, consF, nilF] = "=" : map (findFreeSymbol sig) ["comma", "cons","nil"]
       clauseRules :: [(String, RuleN PS v)]
       clauseRules =
         -- The counter for u_i is global,
         -- the list of vars and the fresh generator are local to each clause.
         -- We use a State Transformer on top of a state monad.
         -- Several StateT computations are run inside one single State computation
          concat $ runSupply (mapM (runClause . toRule) clauses)
       runClause = (`evalStateT` (toEnum <$> [0..]))
                 . (`evalStateT` (mempty :: Map String Term.Var))
                 . (`evalStateT` (mempty :: Set v))
       toRule (t1 :=: t2  :- cc) = toRule (Pred equalF [t1,t2] :- cc)
       toRule (Is  t1 t2  :- cc) = toRule (Pred equalF [t1,t2] :- cc)
       toRule (Pred id tt :- (filter (/= Cut) -> [])) = do
         tt' <- mapM toTerm tt
         return [(id, term (InId id) tt' :-> term (OutId id) tt')]
       toRule (Pred id tt :- (filter (/= Cut) -> gg)) = do
         tt'  <- mapM toTerm tt
         modify (getVars tt' `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (InId id) tt' :-> rhs_0
             r_n = lhs_n :-> term (OutId id) tt'
         return $ zip (repeat id) (r_0 : r_n : mid_r {- :: [Rule BasicPS]-})

       mkRhs (Pred id tt) = do
         vv  <- toList <$> get
         tt' <- mapM toTerm tt
         i   <- next
         return (term (UId i) (term (InId id) tt' : map Pure vv))
       mkRhs (f :=: g) = mkRhs (Pred equalF [f,g])
       mkRhs (Is f  g) = mkRhs (Pred equalF [f,g])

       mkLhs (Pred id tt) = do
         vv  <- toList <$> get
         tt' <- mapM toTerm tt
         modify(getVars tt' `mappend`)
         i   <- current
         return (term (UId i) (term (OutId id) tt' : map Pure vv))
       mkLhs (f :=: g) = mkLhs (Pred equalF [f,g])
       mkLhs (Is f  g) = mkLhs (Pred equalF [f,g])

       toTerm = foldTermM toVar f where
--         f :: (MonadNext m, TRSC f, T PS :<: f) => TermF (Term.Term f) -> m (Term.Term f)
         f(Prolog.Term id tt) = return $ term (FunctorId id') tt where
            id' = map (\c -> if isSpace c then '_' else c) id
         f(Tuple   tt) = return $ term (FunctorId commaF) tt
         f(Cons h t)   = return $ term (FunctorId consF) [h, t]
         f Nil         = return $ constant (FunctorId nilF)
         f Wildcard    = Pure <$> freshVar
         f (String s)  = return (constant (FunctorId ('\"' : s ++ "\"")))
         f (Int i)
            |i>0       = return (iterate (term1 (FunctorId "succ")) (constant (FunctorId "zero")) !! fromInteger i)
            |otherwise = return (iterate (term1 (FunctorId "pred")) (constant (FunctorId "zero")) !! fromInteger i)
         f (Float f)   = return $ constant (FunctorId $ show f)
         toVar (VName id)  = do
           env <- lift get
           case Map.lookup id env of
             Nothing -> do Var _ i <- freshVar
                           let v' = Var (Just id) i
                           lift(put (Map.insert id v' env))
                           return2 v'
             Just v  -> return2 v
         toVar (VAuto  id) = return (Term.var id)


Right preludePl = $(do
                     pgm <- runIO (readFile "prelude.pl")
                     either (error.show) (\_ ->[| parse Prolog.program "prelude.pl" pgm|]) (parse Prolog.program "prelude.pl" pgm)
                   )

skTransformAF = AF.mapSymbols InId

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

prologP_labelling_sk :: (PolyHeuristicN heu LPS, PolyHeuristicN heu LPId, v ~ Term.Var, MonadFree ProofF m) =>
                        MkHeu heu -> PrologProblem v -> m (ProblemG LPId v)
prologP_labelling_sk mkHeu p0@(Problem Prolog{..} _ _)
  | null goals = success (LabellingSKP []) p0
  | otherwise  = mall problems
   where trs      = skTransform program
         problems = do
                       goal_lp <- skTransformAF <$> goals
                       let goal_lps = AF.mapSymbols' (flip Labelling) goal_lp
                       ((trs', pi), modes) <- toList $ labellingTrans mkHeu goal_lp trs
                       let pp' = mkGoalProblem mkHeu GNarrowingModes{pi = pi, goal = goal_lps} trs'
                             -- It is not necessary to fix pi to filter the same for the marked version of a symbol.
                             -- However in practice if we recompute the filtering we obtain the same for the symbols
                             -- that intervene in pairs (and we don't care about those which don't)
                       return $ orP (LabellingSKP modes) p0 (map return pp')


labellingTrans :: (Ord v, Ppr v) => PolyHeuristicN heu LPS => MkHeu heu -> AF_ PS -> NarradarTRS PS v -> Set((NarradarTRS LPS v, AF_ LPS), [LS])
labellingTrans _ _ (rules -> []) = Set.singleton mempty
labellingTrans mkH goalAF trs@PrologTRS{} = unEmbed $ runWriterT $ do
--    let trs0 :: NarradarTRS LPS BasicLPS
    trs0 <- (prologTRS' . mconcat) `liftM` (
             liftM2 (++) (sequence [insertNewMode (f, pp) | (InId f, pp) <- AF.toList (AF.init trs)])
                         (sequence [insertNewMode (f, pp)
                                   | (InId f, pp) <- AF.toList goalAF
                                   ,  InId f `Set.member` allSymbols(getSignature trs)
                                   , pp /= iFun trs (InId f)]))
    let af0  = AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList goalAF] `mappend` AF.init trs0
    -- ("Rules added:\n" ++ unlines (map show $ Types.rules added) ) $
    trace (unlines(map showPpr $ rules trs0) ++ "\n" ++ showPpr af0) $
     fix invariantEV (trs0, af0)
 where
  heuristic = mkHeu mkH trs'

  trs'@(PrologTRS rr sig) = convert trs

--  insertNewMode :: NarradarTRS (Labelled id) f' -> (Labelled id, [Int] -> [Int]) -> NarradarTRS (Labelled id) f'
  insertNewMode (id,pp) | trace ("insertNewMode " ++ show (id,pp)) False = undefined
  insertNewMode (id, pp) = tell [Labelling pp id] >>
                           return (Set.fromList [ (pred, l `setLabel` Labelling pp :-> r `setLabel` Labelling pp)
                                                 | (pred, l :-> r) <- toList rr
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

labellingTrans _ af p = R.return ((convert p, convert af), [])

iFun sig f = [1.. getArity sig f]
