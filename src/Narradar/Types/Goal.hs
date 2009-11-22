{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances, FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Narradar.Types.Goal where

import Control.Applicative hiding (Alternative(..), many, optional)
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

data Goal id = Goal {goalId::id, goalArgs::[Mode]} deriving (Eq, Ord, Show)
data Mode = G | V deriving (Eq, Bounded, Show)

deriving instance Ord Mode

instance Functor Goal where fmap f (Goal id mm) = Goal (f id) mm


goalP  = Goal <$> TRSParser.identifier <*> modesP <* optional dot
modesP = P.parens (commaSep modeP) <|> return []
modeP  = lexeme ((oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V))

parseGoal :: String -> Either ParseError [Goal String]
parseGoal = parse (TRSParser.whiteSpace >> many (goalP <* TRSParser.whiteSpace)) "GOAL"


mkGoalAF (Goal f mm) = AF.singleton f [i | (G,i) <- zip mm [1..]]
instance Pretty Mode where pPrint G = text "b"; pPrint V = text "f"

instance Pretty id => Pretty (Goal id) where pPrint (Goal id modes) = pPrint id <> parens(sep$ punctuate comma $ modes)
instance Pretty (Goal String) where pPrint (Goal id modes) = text id <> parens(sep$ punctuate comma $ modes)


pPrintGoalAF :: (String ~ id, Ord id, Show id) => Signature id -> AF_ id -> Doc
pPrintGoalAF sig pi = vcat [ pPrint (Goal f mm) | (f,pp) <- AF.toList pi
                                           , f `Set.member` getDefinedSymbols sig
                                           , let mm = [if i `elem` pp then G else V | i <- [1..getArity sig f] ]]
