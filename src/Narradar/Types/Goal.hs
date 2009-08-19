{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
module Narradar.Types.Goal where

import Control.Applicative hiding (Alternative(..), many, optional)
import Data.Term.Rules
import qualified Data.Set as Set
import qualified TRSParser
import TRSTypes(Mode(..))
import qualified TRSTypes (TermF(..))
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Applicative ()

import Narradar.Types.ArgumentFiltering (AF_)
import qualified Narradar.Types.ArgumentFiltering as AF
import Narradar.Framework.Ppr hiding (char)

data Goal id = Goal {goalId::id, goalArgs::[Mode]} deriving (Eq, Ord, Show)
instance Ppr Mode where ppr G = text "b"; ppr V = text "f"
deriving instance Ord Mode

instance Functor Goal where fmap f (Goal id mm) = Goal (f id) mm

mkGoalAF (Goal f mm) = AF.singleton f [i | (G,i) <- zip mm [1..]]

goalP = do
  TRSTypes.Term id tt <- TRSParser.goal
  optional (char '.')
  return (Goal id tt)

parseGoal :: String -> Either ParseError [Goal String]
parseGoal = parse (TRSParser.whiteSpace >> many (goalP <* TRSParser.whiteSpace)) ""

pprGoalAF :: (String ~ id, Ord id, Show id) => Signature id -> AF_ id -> Doc
pprGoalAF sig pi = vcat [ pprGoal (Goal f mm) | (f,pp) <- AF.toList pi
                                              , f `Set.member` allSymbols sig
                                              , let mm = [if i `elem` pp then G else V | i <- [1..getArity sig f] ]]

--type Goal id = T id Mode
pprGoal :: Ppr id => Goal id -> Doc
pprGoal (Goal id modes) = ppr id <> parens(sep$ punctuate comma $ map (text.show) modes)
