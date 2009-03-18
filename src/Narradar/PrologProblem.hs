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

module Narradar.PrologProblem (inferType, prologP_sk, prologP_labelling_sk, skTransform) where

import Control.Applicative
import Control.Arrow
import Control.Exception (assert)
import Control.Monad.Error (Error)
import Control.Monad.State
import Control.Monad.Writer
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.HashTable (hashString)
import Data.List (partition, isSuffixOf, isPrefixOf, delete, sort, groupBy, find)
import Data.Maybe
import Data.Monoid
import Data.Foldable (toList, notElem)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Language.Haskell.TH (runIO)
import Text.ParserCombinators.Parsec (parse, ParseError, getInput)
import Text.XHtml (Html, toHtml)

import Language.Prolog.Syntax (TermF(..), VName(..), Clause, ClauseF(..), Program, AtomF(..), Atom, Ident, Term, In(..), Atom, foldInM)
import qualified Language.Prolog.Syntax as Prolog
import qualified Language.Prolog.Parser as Prolog (program, clause, query, whiteSpace, ident)
import Language.Prolog.TypeChecker (infer, TypeAssignment)

import Lattice (Lattice)
import TRS.FetchRules -- for the Error ParseError instance
import TRS (Var)

import Narradar.ArgumentFiltering (AF_, AF, typeHeu, innermost, MkHeu, mkHeu, Heuristic(..))
import qualified Narradar.ArgumentFiltering as AF
import Narradar.Propositional ((\/), (/\), (-->), Formula)
import qualified Narradar.Propositional as Prop
import Narradar.DPairs
import Narradar.Types hiding (Var,Term,In, program)
import qualified Narradar.Types as TRS
import Narradar.NarrowingProblem
import Narradar.Proof
import Narradar.ExtraVars
import Narradar.Utils ((<$$>),(..&..), mapLeft, on, fmap2, trace)

import Prelude hiding (and,or,notElem,pi)

inferType (Problem Prolog{..} _ _) = infer program

-- ----------------
-- Transformations
-- ----------------

{-# off SPECIALIZE prologP_sk :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# pff SPECIALIZE prologP_sk :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
prologP_sk :: AF.PolyHeuristic heu PId BasicPId => MkHeu heu -> PrologProblem -> ProblemProofG PId Html BasicPId
prologP_sk mkHeu p@(Problem Prolog{..} _ _) =
   andP PrologSKP p
     [ return p
         | goal <- goals
         , let pi = AF.mapSymbols InId goal :: AF_ PS
         , p <- mkGoalProblem mkHeu GNarrowingModes{pi,goal=pi} trs]
  where trs   = skTransform program

encodeToSat :: forall f id trs . (TRS trs id f, T id :<: f) => trs -> [Goal id] -> Formula (id, Int)
encodeToSat trs gg = encProb where
  encGoals        = Prop.and [ Prop.var (f,i) | T f mm <- gg, (i,G) <- zip [1..] mm]
  encProb         = Prop.and (map encRule $ TRS.rules trs)
  encRule (l:->r) = Prop.and [ Prop.or [ p `inside` r | p <- pp ] --> Prop.or [ p' `inside` l
                                                                              | p' <- fromMaybe [] (Map.lookup v varsPos_l)]
                             | (v,pp) <- varsPos r]
      where varsPos_l = Map.fromList (varsPos l)
            varsPos   = map (uncurry (,) . first head . unzip)
                      . groupBy ((==) `on` fst) . sort . map (\v -> (dropNote v, note v)) . vars' . annotateWithPos
            (i:p) `inside` (open -> Just(T (f::id) tt)) = Prop.var (f,i) /\ p `inside` (tt!!i)
            [] `inside` _ = Prop.true
            _ `inside` _  = Prop.false

skTransform :: [Clause] -> NarradarTRS PS BasicPS
skTransform (addMissingPredicates -> clauses) = prologTRS clauseRules where
       sig = getSignature clauses

       findFreeSymbol :: String -> String
       findFreeSymbol pre = fromJust $ find (`Set.notMember` allSymbols sig) (pre : [pre ++ show i | i <- [0..]])
       [equalF] = map findFreeSymbol ["equal"]

       clauseRules :: [(Ident, Rule BasicPS)] = concat $ (`evalState` [0..]) $
         -- The counter is global, the list of vars is local to each clause
         -- We use a State Transformer on top of a state monad.
         -- Several StateT computations are run inside one single State computation
         evalStateT (mapM toRule clauses) mempty
       toRule (Pred id tt :- []) = return$
         let tt' = evalState(mapM toTerm tt) [0..] in  -- This evalState is for the MonadFresh in toTerm
          [(id, term (InId id) tt' :-> term (OutId id) tt')]
       toRule (Pred id tt :- (filter (/= Cut) -> gg)) = do
         let tt' = evalState(mapM toTerm tt) [0..]
         modify (Set.fromList(concatMap vars' tt') `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (InId id) tt' :-> rhs_0
             r_n = lhs_n :-> term (OutId id) tt'
         return $ zip (repeat id) (r_0 : r_n : mid_r :: [Rule BasicPS])

       mkRhs (Pred id tt) = do
         vv <- toList <$> get
         let tt' = evalState(mapM toTerm tt) [0..]
         i <- lift fresh
         return (term (UId i :: PS) (term (InId id) tt' : vv))
       mkRhs (f :=: g) = mkRhs (Pred equalF [f,g])
       mkRhs (Is f  g) = mkRhs (Pred equalF [f,g])

       mkLhs (Pred id tt) = do
         vv <- toList <$> get
         let tt' = evalState(mapM toTerm tt) [50..]
         modify(Set.fromList(concatMap vars' tt') `mappend`)
         i <- lift current
         return (term (UId i :: PS) (term (OutId id) tt' : vv))
       mkLhs (f :=: g) = mkLhs (Pred equalF [f,g])
       mkLhs (Is f  g) = mkLhs (Pred equalF [f,g])

       toTerm = foldInM f where
--         f :: (MonadFresh m, TRSC f, T PS :<: f) => TermF (TRS.Term f) -> m (TRS.Term f)
         f(Term id tt) = return $ term (FunctorId id) tt
         f(Tuple   tt) = return $ term (FunctorId "','") tt
         f Wildcard    = var   <$>fresh
         f (Int i)
            |i>0       = return (iterate (TRS.term1 (FunctorId "succ")) (constant (FunctorId "zero")) !! fromInteger i)
            |otherwise = return (iterate (TRS.term1 (FunctorId "pred")) (constant (FunctorId "zero")) !! fromInteger i)
         f (Float f)   = return $ constant (FunctorId $ show f)
         f(Var v)      = return $ toVar v
         toVar (VName id)    = var' (Just id) (abs$ fromIntegral $ hashString id)
         toVar (Auto  id)    = var id


Right preludePl = $(do
                     pgm <- runIO (readFile "prelude.pl")
                     either (error.show) (\_ ->[| parse Prolog.program "prelude.pl" pgm|]) (parse Prolog.program "prelude.pl" pgm)
                   )
preludePreds = Set.fromList [ f | Pred f _ :- _ <- preludePl]
addMissingPredicates cc
  | Set.null undefinedPreds = cc
  | otherwise
  = (if insertPrelude then cc' else cc)  `mappend`
    [Pred f (take (getArity sig f) vars) :- []
     | f <- toList undefinedPreds, f `Set.notMember` preludePreds]

   where vars = [Prolog.var ("X" ++ show i) | i <- [0..]]
         undefinedPreds = Set.fromList [ f | f <- toList (definedSymbols sig `Set.difference` definedPredicates)]
         insertPrelude  = not $ Set.null (Set.intersection undefinedPreds preludePreds)
         sig            = getSignature cc
         definedPredicates = Set.fromList [ f | Pred f _ :- _ <- cc]
         findFreeName pre  = fromJust $ find (`Set.notMember` allSymbols sig)
                                              (pre : [pre ++ show i | i <- [0..]])
         cc' = foldr renamePred (cc `mappend` preludePl) (toList repeatedIdentifiers)
         repeatedIdentifiers = preludePreds `Set.intersection` definedPredicates
         renamePred f = fmap2 (rename (findFreeName f))
         rename f' (Pred f tt) | f == f' = Pred f' tt
         rename _ x = x

{-# off SPECIALIZE prologP_labelling_sk :: Problem BBasicId -> ProblemProofG LId Html BBasicLId #-}

prologP_labelling_sk :: (AF.PolyHeuristic heu LPS BasicLPS, AF.PolyHeuristic heu LPId BasicLPId) => MkHeu heu -> PrologProblem -> ProblemProofG LPId Html BasicLPId
prologP_labelling_sk mkHeu p@(Problem Prolog{..} _ _)
  | null goals = success (LabellingSKP []) p (toHtml "There are no queries to analyze")
  | otherwise = mall problems
   where trs = skTransform program
         problems = do goalAF <- AF.mapSymbols InId <$> goals
                       ((trs', pi), modes) <- toList $ labellingTrans mkHeu goalAF trs
                       let goal     = AF.mapSymbols' (flip Labelling) goalAF
                           pp'      = mkGoalProblem mkHeu GNarrowingModes{pi, goal} trs'
                       return $ orP (LabellingSKP modes) p (map return pp')


labellingTrans :: AF.PolyHeuristic heu LPS BasicLPS => MkHeu heu -> AF_ PS -> NarradarTRS PS BasicPS -> Set((NarradarTRS LPS BasicLPS, AF_ LPS), [Labelled String])
labellingTrans _ _ (rules -> []) = Set.singleton mempty
labellingTrans mkH goalAF trs@PrologTRS{} = unEmbed $ runWriterT $ do
--    let trs0 :: NarradarTRS LPS BasicLPS
    trs0 <- (prologTRS' . mconcat) <$> (
             (++) <$> sequence [insertNewMode (f, pp) | (InId f, pp) <- AF.toList (AF.init trs)]
                  <*> sequence [insertNewMode (f, pp) | (InId f, pp) <- AF.toList goalAF
                                                      , InId f `Set.member` allSymbols(getSignature trs)
                                                      , pp /= iFun trs (InId f)])
    let af0  = AF.fromList [ (Labelling pp f, pp) | (f,pp) <- AF.toList goalAF] `mappend` AF.init trs0
    -- ("Rules added:\n" ++ unlines (map show $ Types.rules added) ) $
    trace (unlines(map show $ rules trs0) ++ "\n" ++ show af0) $
     fix invariantEV (trs0, af0)
 where
  heuristic = mkHeu mkH trs' --innermost af t p -- typeHeu assig af t p

  trs'@(PrologTRS rr sig) = convert trs

--  insertNewMode :: NarradarTRS (Labelled id) f' -> (Labelled id, [Int] -> [Int]) -> NarradarTRS (Labelled id) f'
  insertNewMode (id, pp) = tell [Labelling pp id] >>
                           return (Set.fromList [ (pred, l  `setLabel` pp :-> r `setLabel` pp)
                                                 | (pred, l :-> r) <- toList rr
                                                 ,  pred == id])
  invariantEV f (trs@(PrologTRS rr _), af)
      | ((pred,rule,pos):_) <- extra = cutEV pred rule pos (trs,af) >>= f
      | otherwise  = return (trs, af)
      where extra = [(pred, r, note (head ev))
                             | (pred,r) <- toList rr
                             , let ev = extraVars (AF.apply af (annotateWithPos <$> r))
                             , not (null ev)]
  cutEV pred rule@(l:->r) pos (trs@(PrologTRS rr _), af) = do
      (f, i) <- lift $ embed $ runHeu heuristic af r pos
      trace ("pred: " ++  pred ++ ", symbol:" ++ show f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ show (AF.apply af rule)) $ return ()
      case unlabel f of
        InId f_pred -> do
         let (open -> Just (T u@(unlabel -> UId{} :: PS) ( (open -> Just (T g@(unlabel -> InId{}) vv2)) : vv1))) = r
             f'  = assert (f==g) $ mapLabel (delete i) (delete i $ iFun trs g) g
             r' = term u (term f' vv2 : vv1)
             changes1 =  Set.insert (pred, l:->r') . Set.delete (pred,rule)
             changes2 x = if f' `notElem` (getDefinedSymbols trs) then  (mappend x) <$> insertNewMode (f_pred, labelling f') else return x
             changes3 = foldr (.) id
                        [ Set.insert (pred',outrule') . Set.delete (pred',outrule)
                                | (pred', outrule@(l :-> r)) <- toList rr
                                , (open -> Just (T u' ( (open -> Just (T p_out@(unlabel -> OutId h) vv2)) : vv1))) <- [l]
                                , u == u', h == f_pred
                                , let outrule' = term u (term (mapLabel (delete i) (delete i $ iFun trs p_out)  p_out) vv2 : vv1) :-> r]
         trs'@(PrologTRS rr' _) <- (prologTRS' .changes1 . changes3) <$> changes2 rr
         let af' = af `mappend` AF.singleton f' (labelling f') `mappend` AF.init trs'
             common = Set.intersection rr' rr; added = rr' `Set.difference` common; deleted = rr `Set.difference` common
         trace ("Added " ++ show (Set.size added) ++ " rules and deleted " ++ show (Set.size deleted) ++"\n" ++
                "Rules added:\n" ++ unlines (map (show.snd) $ toList added) ++"\nRules deleted:\n" ++ unlines (map (show.snd) $ toList deleted) ++
                "\n" ++ unlines(map (show.snd) $ toList rr') ++ "\n" ++ show af') $ return ()
         R.return (trs', af')
        _ -> R.return (trs, AF.cut f i af)

labellingTrans _ af p = R.return ((convert p, convert af), [])
iFun sig f = [1.. getArity sig f]

-- RMonad instance for WriterT
-- --------------------------

instance (Monoid s) => R.Suitable (WriterT s m) a where
   data R.Constraints (WriterT s m) a = WriterTConstraints
   constraints _ = WriterTConstraints

instance (Monad m, Monoid s) => R.RFunctor (WriterT s m) where
   fmap = fmap

instance (Monoid s, Monad m) => R.RMonad (WriterT s m) where
   return = return
   (>>=) = (>>=)
   fail = fail
