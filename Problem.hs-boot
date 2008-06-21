module Problem where

import Types(TRS)

data Problem_ a = Problem  ProblemType a a
     deriving (Eq,Show)

type Problem f = Problem_ (TRS f)

data ProblemType = Rewriting | Narrowing
     deriving (Eq, Show)
