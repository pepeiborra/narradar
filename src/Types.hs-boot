module Types where

import TRS

data Identifier = IdFunction String | IdDP String | AnyIdentifier
instance Eq   Identifier
instance Ord  Identifier
instance Show Identifier

data Problem_ a = Problem {typ::ProblemType, trs,dps::a}
instance Eq a   => Eq   (Problem_ a)
instance Show a => Show (Problem_ a)
instance Functor Problem_

type Problem f = Problem_ (TRS Identifier f)

data ProblemType = Rewriting
                 | Narrowing  | NarrowingModes Goal
                 | BNarrowing | BNarrowingModes Goal | LBNarrowingModes Goal
                 | Prolog Goal

instance Eq   ProblemType
instance Show ProblemType

data Mode = G | V
type Goal = T String Mode
instance Show    Mode
instance Eq      Mode
instance Bounded Mode