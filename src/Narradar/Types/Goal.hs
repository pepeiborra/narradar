{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances, FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Narradar.Types.Goal where

import Control.Applicative hiding (Alternative(..), many, optional)
import Control.DeepSeq
import Control.Monad.Free
import Data.Bifunctor
import qualified Data.Set as Set
import Data.Term.Rules
import qualified TRSParser
import qualified TRSTypes (TermF(..))
import qualified Narradar.Utils.Parse as P
import Narradar.Utils.Parse hiding (parens, comma)

import Narradar.Types.ArgumentFiltering (AF_)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework.Ppr hiding (char)
import Narradar.Types.Term

import Debug.Hoed.Observe

data GoalF id a = Goal {goalId::id, goalArgs::[a]} deriving (Eq, Ord, Show)
type Goal id = GoalF id Mode
data Mode = G | V deriving (Eq, Ord, Bounded, Show)

goal :: id -> [Mode] -> Goal id
goal = Goal

termToGoal :: Term (TermF id)  Mode -> Goal id
termToGoal (Impure (Term id mm)) = Goal id [m | Pure m <- mm]

instance NFData Mode where rnf G = (); rnf V = ()

--instance Functor GoalF where fmap f (Goal id mm) = Goal id (f mm)
instance Bifunctor GoalF where
  bimap fid fmm (Goal id mm) = Goal (fid id) (map fmm mm)

goalP  = Goal <$> TRSParser.identifier <*> modesP <* optional dot
modesP = P.parens (commaSep modeP) <|> return []
modeP  = lexeme ((oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V))

parseGoal :: String -> Either ParseError [Goal String]
parseGoal = parse (TRSParser.whiteSpace >> many (goalP <* TRSParser.whiteSpace)) "GOAL"


mkGoalAF (Goal f mm) = AF.singleton f [i | (G,i) <- zip mm [1..]]
instance Pretty Mode where pPrint G = text "b"; pPrint V = text "f"

instance (Pretty id, Pretty a) => Pretty (GoalF id a) where
    pPrint (Goal id [])    = pPrint id
    pPrint (Goal id modes) = pPrint id <> parens(sep$ punctuate comma $ modes)
instance Pretty a => Pretty (GoalF String a) where
    pPrint (Goal id [])    = text id
    pPrint (Goal id modes) = text id <> parens(sep$ punctuate comma $ modes)


pPrintGoalAF :: (String ~ id, Ord id, Show id) => Signature id -> AF_ id -> Doc
pPrintGoalAF sig pi = vcat [ pPrint (Goal f mm) | (f,pp) <- AF.toList pi
                                           , f `Set.member` getDefinedSymbols sig
                                           , let mm = [if i `elem` pp then G else V | i <- [1..getArity sig f] ]]

instance Observable Mode where observer = observeBase

instance Observable id => Observable (Goal id) where observer (Goal id args) = send "Goal" (return Goal << id << args)
