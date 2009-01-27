{-# LANGUAGE TypeSynonymInstances #-}
module Prolog where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.HashTable (hashString)
import Data.Monoid
import Data.Foldable (toList)
import qualified Data.Set as Set
import Language.Prolog.Syntax (TermF(..), VName(..), ClauseF(..), Program, PredF(..), Pred, Term, In(..))
import Types hiding (Var,Term,In)
import qualified Types as TRS
import NarrowingProblem

mkPrologProblem = mkSKPrologProblem

mkMyPrologProblem :: Goal -> Program -> Problem BasicId
mkMyPrologProblem g clauses = mkLBNDPProblem (Just g) trs
    where trs   = mkTRS(andRules ++ clauseRules)
          clauseRules         = map toRule clauses
          toRule (g :- [])    = toTerm g :-> true
          toRule (g :- b)     = toTerm g :-> foldr1 and (map toTerm b)
          andRules =
              [ and true true  :-> true
              , and true false :-> false
              , and false true :-> false
              , and false false :-> false ]
          and   = term2 "and"
          true  = constant "true"
          false = constant "false"

mkSKPrologProblem  :: Goal -> Program -> Problem BasicId
mkSKPrologProblem  (T g modes) clauses = mkLBNDPProblem (Just g') (mkTRS $ concat clauseRules)
 where g' = T (g ++ "_in") modes
       clauseRules = (`evalState` mempty) ((`evalStateT` [0..])  (mapM toRule clauses))
       toRule (Pred id tt :- []) = return$ let tt' = map toTerm tt in [term (id ++ "_in") tt' :-> term (id++"_out") tt']
       toRule (Pred id tt :- gg) = do
         let tt' = map toTerm tt
         lift $ modify (Set.fromList(concatMap vars' tt') `mappend`)
         rhs_0  <- mkRhs (head gg)
         mid_r  <- forM (gg `zip` tail gg) $ \(c,sc) -> (:->) <$> mkLhs c <*> mkRhs sc
         lhs_n  <- mkLhs (last gg)
         let r_0 = term (id ++ "_in") tt' :-> rhs_0
             r_n = lhs_n :-> term (id ++ "_out") tt'
         return (r_0 : r_n : mid_r)

       mkRhs (Pred id tt) = do
         vv <- toList <$> lift get
         let tt' = map toTerm tt
         i <- fresh
         return (term ("u_" ++ show i) (term (id ++ "_in") tt' : vv))

       mkLhs (Pred id tt) = do
         vv <- toList <$> lift get
         let tt' = map toTerm tt
         lift $ modify(Set.fromList(concatMap vars' tt') `mappend`)
         i <- current
         return (term ("u_" ++ show i) (term (id ++ "_out") tt' : vv))


class ToTerm t where toTerm :: t -> TRS.Term Basic
instance ToTerm Pred where
   toTerm (Pred id tt) = term id (map toTerm tt)
instance ToTerm Term where
   toTerm = foldIn toTerm' where
          toTerm'(Term id tt) = term id tt
          toTerm'(Var v)      = toVar v
          toVar (VName id)    = var' (Just id) (fromIntegral $ hashString id)
          toVar (Auto  id)    = var id

foldIn f (In t) = f (fmap (foldIn f) t)

instance Monad m => Applicative (StateT s m) where pure = return; (<*>) = ap