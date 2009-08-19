module Narradar.Examples where

import Prelude hiding (div,succ, quot)

import Narradar.Types.Problem
import Narradar.Types.DPIdentifiers
import Narradar.Types.Term
import Narradar.Types.Var
import Narradar.Utils

(x:y:z:a:b:c:_) = map var [0..]

-- ---------------
-- Peano addition
-- ---------------
succ x = term "s" [x]
zero   = term "0" []
x +: y = term "add" [x,y]

peano = [ zero   +: y :-> y
        , succ x +: y :-> succ (x +: y)]

plus1 = [ zero   +: y :-> y
        , succ x +: y :-> x +: succ y]

plus2 = [ x +: zero   :-> x
        , x +: succ y :-> succ (y +: x)]

plus3 = [ x +: zero   :-> x
         , x +: succ y :-> succ x +: y]

-- --------------------------------------------------------
-- Normalization of formulas with propositional connectives
-- --------------------------------------------------------
gt x y = term "gt" [x,y]
ge x y = term "ge" [x,y]
neg x  = term "neg" [x]
x *: y = term "mul"  [x,y]

norm = [ neg(gt a b) :-> ge b a
       , neg(ge a b) :-> gt b a
       , neg(a +: b) :-> neg a *: neg b
       , neg(a *: b) :-> neg a +: neg b
       , a *: (b+:c) :-> (a*:b)+:(a*:c)
       , (b+:c) *: a :-> (a*:b)+:(a*:c)
       ]

-- --------------------------------------------------------
-- divdiv: quasiLPO orientable but not strictLPO orientable
-- --------------------------------------------------------
div x y = term "div" [x,y]
e = term "e" []
i x = term "i" [x]

divdiv = [ div x e         :-> i x
         , i (div x y)     :-> div y x
         , div (div x y) z :-> div y (div (i x) z)
         ]

-- ----------------------------------
-- quot: non monotonic LPO orientable
-- ----------------------------------

quot x y = term "quot"  [x,y]
x -: y   = term "minus" [x,y]

minus = [ x      -: zero   :-> x
        , succ x -: succ y :-> x -: y ]

minusquot = mapTermSymbols IdFunction <$$>
       (minus ++
       [ quot zero (succ y)     :-> zero
       , quot (succ x) (succ y) :-> succ (quot (x -: y) (succ y)) ])


minusquotPairs = getPairs minusquot

{-
minusquotP  = mkProblem Rewriting minusquot minusquotPairs
minusquotP1 = mkProblem Rewriting minusquot (take 1 minusquotPairs)
minusquotP2 = mkProblem Rewriting minusquot [minusquotPairs !! 1]
-}
-- -----
-- large
-- -----
true  = term "true"  []
false = term "false" []
iff b t e = term "if" [b,t,e]

large = minus ++
        [ ge x zero :-> true
        , ge zero (succ x) :-> false
        , ge (succ x) (succ y) :-> ge x y
        ] ++
        [ div x y :-> iff (ge x y) x y
        , iff true (succ x) (succ y) :-> succ (div (x -: y) (succ y))
        , iff false x (succ y) :-> zero]

-- --------------------------
-- nonterm: non terminating
-- --------------------------

nonterm1 = [term "f" [term "s" [x]] :-> term "f" [term "s" [x]]]
nonterm2 = [term "f" [x] :-> term "f" [x]]


-- -------
-- lpairs
-- -------

f x = term "f" [x]

lpairs = [f (f x) :-> x]