{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}


module PrologProblem where

import Control.Applicative
import Control.Arrow
import Control.Monad.Error (Error)
import Control.Monad.State
import Control.Monad.Writer
import qualified Control.RMonad as R
import Control.RMonad.AsMonad
import Data.HashTable (hashString)
import Data.List (partition, isSuffixOf, isPrefixOf, delete)
import Data.Maybe
import Data.Monoid
import Data.Foldable (toList, notElem)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Text.ParserCombinators.Parsec (parse, ParseError, getInput)
import Text.XHtml

import ArgumentFiltering (AF_, AF, typeHeu)
import qualified ArgumentFiltering as AF
import DPairs
import Language.Prolog.Syntax (TermF(..), VName(..), Clause, ClauseF(..), Program, PredF(..), Pred, Term, In(..), Atom)
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Parser (program)
import Language.Prolog.TypeChecker (infer, TypeAssignment)
import Types hiding (Var,Term,In, program)
import qualified Types as TRS
import NarrowingProblem
import Proof
import Lattice
import TRS.FetchRules -- for the Error ParseError instance
import Utils ((<$$>),(..&..))

import Prelude hiding (and,or,notElem)

#ifdef DEBUG
import Debug.Trace
#else
trace _ x = x
#endif
--instance Error ParseError

--mkPrologProblem = (return.) . mkPrologProblem
parsePrologProblem pgm gg = do
     let ei_prolog = parse problemParser "input" pgm
     case ei_prolog of
       Left parse_error -> Left $ show parse_error
       Right (cc, specials) ->
          let gg' = queries specials
              all_goals = mapM parseGoal (gg ++ gg')
          in case all_goals of
            Left e   -> Left $ show e
            Right [] -> Left "A goal must be supplied in order to solve a Prolog termination problem"
            Right all-> Right (mkPrologProblem all cc)


--mkSKPrologProblem  :: [Goal] -> Program -> ProblemProof res BasicId
--prologP_sk :: Problem BasicId -> ProblemProof Html BasicId
--prologP_sk :: Problem BBasicId -> ProblemProof Html BBasaicId

{-# SPECIALIZE prologP_sk :: Problem BBasicId -> ProblemProof Html BBasicId #-}
{-# SPECIALIZE prologP_sk :: ProblemG LId BBasicLId -> ProblemProofG LId Html BBasicLId #-}
prologP_sk :: forall f id. ( ConvertT Basic f, Bottom :<: f, DPMark f id, Lattice (AF_ id)) => ProblemG id f -> ProblemProofG id Html f
prologP_sk (PrologProblem typ gg clauses) =
   andP PrologSKP (mkPrologProblem gg clauses :: Problem f)
     [mkGoalProblem (FromGoal (T (g ++ "_in") modes) (Just $ infer clauses)) (mkDPProblem BNarrowing $ convert $ skTransform clauses) | T g modes <- gg]

prologP_sk p = return p

skTransform :: [Clause] -> NarradarTRS String Basic
skTransform (addMissingPredicates -> clauses) = prologTRS clauseRules where
       clauseRules :: [(Atom, Rule Basic)] = concat $ (`evalState` [0..]) $
         -- The counter is global, the list of vars is local to each clause
         -- We use a State Transformer on top of a state monad.
         -- Several StateT computations are run inside one single State computation
         evalStateT (mapM toRule clauses) mempty
       toRule (Pred id tt :- []) = return$
         let tt' = evalState(mapM toTerm tt) [0..] in  -- This evalState is for the MonadFresh in toTerm
          [(id, term (id ++ "_in") tt' :-> term (id++"_out") tt')]
       toRule (Pred id tt :- gg) = do
         let tt' = evalState(mapM toTerm tt) [0..]
         modify (Set.fromList(concatMap vars' tt') `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (id ++ "_in") tt' :-> rhs_0
             r_n = lhs_n :-> term (id ++ "_out") tt'
         return $ zip (repeat id) (r_0 : r_n : mid_r)

       mkRhs (Pred id tt) = do
         vv <- toList <$> get
         let tt' = evalState(mapM toTerm tt) [0..]
         i <- lift fresh
         return (term ("u_" ++ show i) (term (id ++ "_in") tt' : vv))

       mkLhs (Pred id tt) = do
         vv <- toList <$> get
         let tt' = evalState(mapM toTerm tt) [50..]
         modify(Set.fromList(concatMap vars' tt') `mappend`)
         i <- lift current
         return (term ("u_" ++ show i) (term (id ++ "_out") tt' : vv))

addMissingPredicates cc
          | sig <- getSignature cc
          , definedPredicates <- Set.fromList [ f | Pred f _ :- _ <- cc]
          = cc `mappend` [ Pred f (take (getArity sig f) vars) :- [] | f <- toList (definedSymbols sig `Set.difference` definedPredicates)]
   where vars = [Prolog.var ("X" ++ show i) | i <- [0..]]

{-# SPECIALIZE prologP_labelling_sk :: Problem BBasicId -> ProblemProofG LId Html BBasicLId #-}

prologP_labelling_sk :: forall f f' id. (Bottom :<: f, MapLabelT f', T id :<: f, Bottom :<: f', DPMark f id, DPMark f' (Labelled id), ConvertT f f', ConvertT Basic f, Ord id, Show id, Lattice (AF_ (Labelled id)))
              => ProblemG id f -> ProblemProofG (Labelled id) Html f'
prologP_labelling_sk p@(PrologProblem typ gg cc) =
    let trs :: NarradarTRS id f = convert $ skTransform cc
        problems = do  T goal mm   <- gg
                       let pp     = [ i | (i,m) <- zip [1..] mm, m == G]
                           goal_f = functionSymbol $ goal++"_in"
                           goalAF = AF.singleton goal_f pp
                           assig  = infer cc
                       (trs', af') <- toList $ labellingTrans goalAF assig trs
                       return (mkGoalProblem (FromAF af' (Just assig)) (mkDPProblem BNarrowing trs'))
    in andP LabellingSKP p problems

--labellingTrans :: AF -> NarradarTRS Identifier BBasicId -> (NarradarTRS (Labelled Identifier) BBasicLId, AF_ (Labelled Identifier))
labellingTrans :: forall id f f'. (Bottom :<: f, MapLabelT f' , DPMark f' (Labelled id), DPMark f id, ConvertT f f', T (Labelled id) :<: f', Bottom :<: f', Ord id, Show id) =>
                  AF_ id -> TypeAssignment -> NarradarTRS id f -> Set(NarradarTRS (Labelled id) f', AF_ (Labelled id))
labellingTrans goalAF assig trs@PrologTRS{} =
    let goalAF' = AF.init trs'' `mappend`
                  AF.fromList [ (Labelling pp f, pp) | (f,pp) <- candidates]

        trs''   = trs' `mappend` prologTRS'(mconcat [ insertMarkedSymbol (Plain f, pp) | (f,pp) <- candidates])
        candidates = [ (f, pp)
                       | (f, pp) <- AF.toList goalAF
                       , "_in" `isSuffixOf` symbol f
                       , f `Set.member` getFunctionSymbols trs
                       , length pp /= getArity trs f]
    in fix invariantEV (trs'', goalAF')
 where
  heuristic af t p = typeHeu assig af t p

  trs'@(PrologTRS rr sig) = convert trs :: NarradarTRS (Labelled id) f'

--  insertMarkedSymbol :: NarradarTRS (Labelled id) f' -> (Labelled id, [Int] -> [Int]) -> NarradarTRS (Labelled id) f'
  insertMarkedSymbol (id, pp) =
    let rr' :: Set (Atom, Rule f') =
                    Set.fromList [ (pred, l  `setLabel` pp :-> r `setLabel` pp)
                                        | (pred, l :-> r) <- toList rr
                                        ,  pred `isPrefixOf` symbol id]
            in rr'
  invariantEV f (trs@(PrologTRS rr _), af)
      | ((pred,rule,pos):_) <- extra = cutEV pred rule pos (trs,af) R.>>= f
      | otherwise  = R.return (trs, af)
      where extra = [(pred, r, note (head ev))
                             | (pred,r) <- toList rr
                             , let ev = extraVars (AF.apply af (annotateWithPos <$> r))
                             , not (null ev)]

  cutEV pred rule@(l:->r) pos (trs@(PrologTRS rr _), af) = unEmbed $ do
      (f,i) <- embed $ heuristic af r pos
      embed$ trace ("pred: " ++  pred ++ ", symbol:" ++ show f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ show (AF.apply af rule)) $
       if "_in" `isSuffixOf` symbol f
        then
         let f_pred = init $ init $ init $ symbol f
             (open -> Just (T (u::Labelled id) ( (open -> Just (T (g::Labelled id) vv2)) : vv1))) = r
             f'  = mapLabel (delete i) (delete i $ iFun trs f) f
             r'  = term u (term f' vv2 : vv1)
             changes1 =  Set.insert (pred, l:->r') . Set.delete (pred,rule)
             changes2 = if f' `notElem` (getDefinedSymbols trs) then (`mappend` insertMarkedSymbol (f, labelling f')) else id
             changes3 = foldr (.) id
                        [ Set.insert (pred',outrule') . Set.delete (pred',outrule)
                                | (pred', outrule@(l :-> r)) <- toList rr
                                , (open -> Just (T u' ( (open -> Just (T (p_out::Labelled id) vv2)) : vv1))) <- [l]
                                , u == u', symbol p_out == f_pred ++ "_out"
                                , let outrule' = term u (term (mapLabel (delete i) (delete i $ iFun trs p_out)  p_out) vv2 : vv1) :-> r]
             trs'@(PrologTRS rr' _) = prologTRS' (changes1 $ changes3 $ changes2 rr) :: NarradarTRS (Labelled id) f'
             af' = af `mappend` AF.singleton f' (labelling f') `mappend` AF.init trs'

         in let common = Set.intersection rr' rr; added = rr' `Set.difference` common; deleted = rr `Set.difference` common
            in trace ("Added " ++ show (Set.size added) ++ " rules and deleted " ++ show (Set.size deleted) ++"\n" ++
                      "Rules added:\n" ++ unlines (map (show.snd) $ toList added) ++"\nRules deleted:\n" ++ unlines (map (show.snd) $ toList deleted)) $
               trace (unlines(map (show.snd) $ toList rr') ++ "\n" ++ show af') $
            R.return (trs', af')
        else R.return (trs, AF.cut f i af)

labellingTrans af _ p = R.return (convert p :: NarradarTRS (Labelled id) f', convert af :: AF_ (Labelled id))

iFun sig f = [1.. getArity sig f]

-- -------------------
-- RHS Bottom tricks
-- -------------------
prologP_sk_rhs :: forall f id. ( ConvertT Basic f, Bottom :<: f, DPMark f id, Lattice (AF_ id)) => ProblemG id f -> ProblemProofG id Html f
prologP_sk_rhs (PrologProblem typ gg clauses) =
   andP PrologSKP_rhs (mkPrologProblem gg clauses :: Problem f)
     [mkGoalProblem_rhs (FromGoal (T (g ++ "_in") modes) (Just $ infer clauses)) (mkDPProblem BNarrowing $ convert $ skTransform clauses) | T g modes <- gg]

prologP_labelling_sk_rhs :: forall f f' id. (Bottom :<: f, MapLabelT f', T id :<: f, Bottom :<: f', DPMark f id, DPMark f' (Labelled id), ConvertT f f', ConvertT Basic f, Ord id, Show id, Lattice (AF_ (Labelled id)))  => ProblemG id f -> ProblemProofG (Labelled id) Html f'
prologP_labelling_sk_rhs p@(PrologProblem typ gg cc) =
    let trs :: NarradarTRS id f = convert $ skTransform cc
        problems = do  T goal mm   <- gg
                       let pp     = [ i | (i,m) <- zip [1..] mm, m == G]
                           goal_f = functionSymbol $ goal++"_in"
                           goalAF = AF.singleton goal_f pp
                           assign = infer cc
                       (trs', af') <- toList $ labellingTrans_rhs goalAF assign trs
                       let goalAF' = af' `mappend` AF.singleton (markDPSymbol(Labelling pp goal_f)) pp
                       return (mkGoalProblem_rhs (FromAF goalAF' (Just assign)) (mkDPProblem BNarrowing trs'))
    in andP LabellingSKP_rhs p problems

labellingTrans_rhs :: forall id f f'. (Bottom :<: f, MapLabelT f' , DPMark f' (Labelled id), DPMark f id, ConvertT f f', T (Labelled id) :<: f', Bottom :<: f', Ord id, Show id) => AF_ id -> TypeAssignment -> NarradarTRS id f -> Set(NarradarTRS (Labelled id) f', AF_ (Labelled id))
labellingTrans_rhs goalAF assig trs@PrologTRS{} =
    let goalAF' = AF.init trs'' `mappend`
                  AF.fromList [ (Labelling pp f, pp) | (f,pp) <- candidates]

        trs''   = trs' `mappend` prologTRS'(mconcat [ insertMarkedSymbol (Plain f, pp) | (f,pp) <- candidates])
        candidates = [ (f, pp)
                       | (f, pp) <- AF.toList goalAF
                       , "_in" `isSuffixOf` symbol f
                       , f `Set.member` getFunctionSymbols trs
                       , length pp /= getArity trs f]
    in fix invariantEV (trs'', goalAF')
 where
  heuristic af t p = Set.singleton $ Set.findMin $ typeHeu assig af t p

  trs'@(PrologTRS rr sig) = convert trs :: NarradarTRS (Labelled id) f'

--  insertMarkedSymbol :: NarradarTRS (Labelled id) f' -> (Labelled id, [Int] -> [Int]) -> NarradarTRS (Labelled id) f'
  insertMarkedSymbol (id, pp) =
    let rr' :: Set (Atom, Rule f') =
                    Set.fromList [ (pred, l  `setLabel` pp :-> r `setLabel` pp)
                                        | (pred, l :-> r) <- toList rr
                                        ,  pred `isPrefixOf` symbol id]
            in rr'
  invariantEV f (trs@(PrologTRS rr _), af)
      | ((pred,rule,pos):_) <- extra = cutEV pred rule pos (trs,af) R.>>= f
      | otherwise  = R.return (trs, af)
      where extra = [(pred, r, note (head ev))
                             | (pred,r) <- toList rr
                             , let ev = extraVars (AF.apply_rhs trs af (annotateWithPos <$> r))
                             , not (null ev)]

  cutEV pred rule@(l:->r) pos (trs@(PrologTRS rr _), af) = unEmbed $ do
      (f,i) <- embed $ heuristic af r pos
      embed$ trace ("pred: " ++  pred ++ ", symbol:" ++ show f ++ ", i: " ++ show i ++ ", pos: " ++ show pos ++ " rule: " ++ show (AF.apply_rhs trs af rule)) $
       if "_in" `isSuffixOf` symbol f
        then
         let f_pred = init $ init $ init $ symbol f
             (open -> Just (T (u::Labelled id) ( (open -> Just (T (g::Labelled id) vv2)) : vv1))) = r
             f'  = mapLabel (delete i) (delete i $ iFun trs f) f
             r'  = term u (term f' vv2 : vv1)
             changes1 =  Set.insert (pred, l:->r') . Set.delete (pred,rule)
             changes2 = if f' `notElem` (getDefinedSymbols trs) then (`mappend` insertMarkedSymbol (f, labelling f')) else id
             changes3 = foldr (.) id
                        [ Set.insert (pred',outrule') . Set.delete (pred',outrule)
                                | (pred', outrule@(l :-> r)) <- toList rr
                                , (open -> Just (T u' ( (open -> Just (T (p_out::Labelled id) vv2)) : vv1))) <- [l]
                                , u == u', symbol p_out == f_pred ++ "_out"
                                , let outrule' = term u (term (mapLabel (delete i) (delete i $ iFun trs p_out)  p_out) vv2 : vv1) :-> r]
             trs'@(PrologTRS rr' _) = prologTRS' (changes1 $ changes3 $ changes2 rr) :: NarradarTRS (Labelled id) f'
             af' = af `mappend` AF.singleton f' (labelling f') `mappend` AF.init trs'

         in let common = Set.intersection rr' rr; added = rr' `Set.difference` common; deleted = rr `Set.difference` common
            in trace ("Added " ++ show (Set.size added) ++ " rules and deleted " ++ show (Set.size deleted) ++"\n" ++
                      "Rules added:\n" ++ unlines (map (show.snd) $ toList added) ++"\nRules deleted:\n" ++ unlines (map (show.snd) $ toList deleted)) $
               trace (unlines(map (show.snd) $ toList rr') ++ "\n" ++ show af') $
            R.return (trs', af')
        else R.return (trs, AF.cut f i af)

labellingTrans_rhs af _ p = R.return (convert p :: NarradarTRS (Labelled id) f', convert af :: AF_ (Labelled id))

-- -------------------------------------------
-- Parsing Prolog problems
-- --------------------------

data PrologSection = Query String | ModeHint String
problemParser = do
  txt <- getInput
  let specials = catMaybes(map f (lines txt))
  res <- program
  return (res,specials)
  where f ('%':'q':'u':'e':'r':'y':':':goal) = Just $ Query goal
        f ('%':'m':'o':'d':'e':':':goal)     = Just $ ModeHint goal
--        f ('t':'y':'p':'e':':':goal)     = Just $ ModeHint goal
        f _ = Nothing

queries xx = [q | Query q <- xx]

class ToTerm t where toTerm :: (TRSC f, T String :<: f, MonadFresh m) => t -> m(TRS.Term f)
instance ToTerm Pred where
   toTerm (Pred id tt) = term id <$> mapM toTerm tt
instance ToTerm Term where
   toTerm = foldInM f where
          f :: (MonadFresh m, TRSC f, T String :<: f) => TermF (TRS.Term f) -> m (TRS.Term f)
          f(Term id tt) = return $ term id tt
          f Wildcard    = var   <$>fresh
          f (Int i)     = return $ constant (show i)
          f (Float f)   = return $ constant (show f)
          f(Var v)      = return $ toVar v
          toVar (VName id)    = var' (Just id) (abs$ fromIntegral $ hashString id)
          toVar (Auto  id)    = var id

foldIn f  (In t) = f    (fmap (foldIn f) t)
--ldInM :: (Monad m) => (TermF a -> m a) -> Term -> m a
foldInM f (In t) = f =<< T.mapM (foldInM f) t
isRight Right{} = True; isRight _ = False

instance Monad m => Applicative (StateT s m) where pure = return; (<*>) = ap
instance Applicative (State s) where pure = return; (<*>) = ap

-- ---------------
-- Naive transform
-- ---------------

--mkMyPrologProblem :: [Goal] -> Program -> ProblemProof res BasicId
--prologP :: Problem BasicBId -> ProblemProof Html BasicBId
prologP :: forall f id. (ConvertT Basic f, Bottom :<: f, DPMark f id, TRSC f, Lattice (AF_ id), Show id, Ord id) => ProblemG id f -> ProblemProofG id Html f
{-# SPECIALIZE prologP :: Problem BBasicId -> ProblemProof Html BBasicId #-}
prologP (PrologProblem typ gg clauses) =
      andP PrologP (mkPrologProblem gg clauses :: ProblemG id f)
               [mkGoalProblem (FromGoal g (Just $ infer clauses)) (mkDPProblem Narrowing trs) | g <- gg]
    where trs = mkTRS(andRules ++ clauseRules)
          clauseRules      = map toRule clauses
          toRule (g :- []) = evalState ((:->) <$> toTerm g <*> pure true) [50..]
          toRule (g :- b)  = evalState ((:->) <$> toTerm g <*> (foldr1 and <$> mapM toTerm b)) [50..]
          andRules :: [Rule Basic] =
              [ and true true  :-> true
              , and true false :-> false
              , and false true :-> false
              , and false false :-> false ]
          and   = term2 "and"
          true  = constant "true"
          false = constant "false"

prologP p = return p
