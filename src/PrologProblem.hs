{-# LANGUAGE PatternGuards, TypeSynonymInstances, NoMonomorphismRestriction #-}
module PrologProblem where

import Control.Applicative
import Control.Monad.Error (Error)
import Control.Monad.State
import Control.Monad.Writer
import Data.HashTable (hashString)
import Data.List (partition)
import Data.Maybe
import Data.Monoid
import Data.Foldable (toList)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Text.ParserCombinators.Parsec (parse, ParseError, getInput)
import Text.XHtml

import Language.Prolog.Syntax (TermF(..), VName(..), Clause, ClauseF(..), Program, PredF(..), Pred, Term, In(..))
import Language.Prolog.Parser (program)
import Types hiding (Var,Term,In, program)
import qualified Types as TRS
import NarrowingProblem
import Proof
import TRS.FetchRules -- for the Error ParseError instance

import Utils ((<$$>))

--instance Error ParseError

mkPrologProblem = (return.) . prologProblem
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


--mkMyPrologProblem :: [Goal] -> Program -> ProblemProof res BasicId
prologP :: Problem BasicId -> ProblemProof Html BasicId
prologP (PrologProblem typ gg clauses) =
      andP PrologP (prologProblem gg clauses)
               [mkBNDPProblem (Just g) trs | g <- gg]
    where trs   = mkTRS(andRules ++ clauseRules)
          clauseRules         = map toRule clauses
          toRule (g :- [])    = evalState ((:->) <$> toTerm g <*> pure true) [50..]
          toRule (g :- b)     = evalState ((:->) <$> toTerm g <*> (foldr1 and <$> mapM toTerm b)) [50..]
          andRules =
              [ and true true  :-> true
              , and true false :-> false
              , and false true :-> false
              , and false false :-> false ]
          and   = term2 "and"
          true  = constant "true"
          false = constant "false"

prologP p = return p

--mkSKPrologProblem  :: [Goal] -> Program -> ProblemProof res BasicId
prologP_sk :: Problem BasicId -> ProblemProof Html BasicId
prologP_sk (PrologProblem typ gg clauses) =
   andP PrologSKP (prologProblem gg clauses)
    [mkBNDPProblem (Just (T (g ++ "_in") modes)) trs | T g modes <- gg]
 where trs = mkTRS $ concat clauseRules
       clauseRules = (`evalState` mempty) ((`evalStateT` [0..])  (mapM toRule clauses))
       toRule (Pred id tt :- []) = return$
         let tt' = evalState(mapM toTerm tt) [50..] in
          [term (id ++ "_in") tt' :-> term (id++"_out") tt']
       toRule (Pred id tt :- gg) = do
         let tt' = evalState(mapM toTerm tt) [50..]
         lift $ modify (Set.fromList(concatMap vars' tt') `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (id ++ "_in") tt' :-> rhs_0
             r_n = lhs_n :-> term (id ++ "_out") tt'
         return (r_0 : r_n : mid_r)

       mkRhs (Pred id tt) = do
         vv <- toList <$> lift get
         let tt' = evalState(mapM toTerm tt) [50..]
         i <- fresh
         return (term ("u_" ++ show i) (term (id ++ "_in") tt' : vv))

       mkLhs (Pred id tt) = do
         vv <- toList <$> lift get
         let tt' = evalState(mapM toTerm tt) [50..]
         lift $ modify(Set.fromList(concatMap vars' tt') `mappend`)
         i <- current
         return (term ("u_" ++ show i) (term (id ++ "_out") tt' : vv))

prologP_sk p = return p

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

class ToTerm t where toTerm :: MonadFresh m => t -> m(TRS.Term Basic)
instance ToTerm Pred where
   toTerm (Pred id tt) = term id <$> mapM toTerm tt
instance ToTerm Term where
   toTerm = foldInM f where
          f :: MonadFresh m => TermF (TRS.Term Basic) -> m (TRS.Term Basic)
          f(Term id tt) = return $ term id tt
          f Wildcard    = var   <$>fresh
          f(Var v)      = return $ toVar v
          toVar (VName id)    = var' (Just id) (abs$ fromIntegral $ hashString id)
          toVar (Auto  id)    = var id

foldIn f  (In t) = f    (fmap (foldIn f) t)
--ldInM :: (Monad m) => (TermF a -> m a) -> Term -> m a
foldInM f (In t) = f =<< T.mapM (foldInM f) t
isRight Right{} = True; isRight _ = False

instance Monad m => Applicative (StateT s m) where pure = return; (<*>) = ap
instance Applicative (State s) where pure = return; (<*>) = ap