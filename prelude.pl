isPlus(zero, X, X).
isPlus(succ(X), zero, succ(X)).
isPlus(succ(X), succ(Y), succ(succ(Z))) :- isPlus(X, Y, Z).
isPlus(succ(X), pred(Y), Z) :- isPlus(X, Y, Z).
isPlus(pred(X), zero, pred(X)).
isPlus(pred(X), succ(Y), Z) :- isPlus(X, Y, Z).
isPlus(pred(X), pred(Y), pred(pred(Z))) :- isPlus(X, Y, Z).
isMinus(X, zero, X).
isMinus(zero, succ(Y), pred(Z)) :- isMinus(zero, Y, Z).
isMinus(zero, pred(Y), succ(Z)) :- isMinus(zero, Y, Z).
isMinus(succ(X), succ(Y), Z) :- isMinus(X, Y, Z).
isMinus(succ(X), pred(Y), succ(succ(Z))) :- isMinus(X, Y, Z).
isMinus(pred(X), succ(Y), pred(pred(Z))) :- isMinus(X, Y, Z).
isMinus(pred(X), pred(Y), Z) :- isMinus(X, Y, Z).
isTimes(X, zero, zero).
isTimes(zero, succ(Y), zero).
isTimes(zero, pred(Y), zero).
isTimes(succ(X), succ(Y), Z) :- ','(isTimes(succ(X), Y, A), isPlus(A, succ(X), Z)).
isTimes(succ(X), pred(Y), Z) :- ','(isTimes(succ(X), Y, A), isMinus(A, succ(X), Z)).
isTimes(pred(X), succ(Y), Z) :- ','(isTimes(pred(X), Y, A), isPlus(A, pred(X), Z)).
isTimes(pred(X), pred(Y), Z) :- ','(isTimes(pred(X), Y, A), isMinus(A, pred(X), Z)).
isDiv(zero, succ(Y), zero).
isDiv(zero, pred(Y), zero).
isDiv(succ(X), succ(Y), zero) :- isMinus(succ(X), succ(Y), pred(Z)).
isDiv(succ(X), succ(Y), succ(Z)) :- ','(isMinus(succ(X), succ(Y), A), isDiv(A, succ(Y), Z)).
isDiv(succ(X), pred(Y), Z) :- ','(isMinus(zero, pred(Y), A), ','(isDiv(succ(X), A, B), isMinus(zero, B, Z))).
isDiv(pred(X), pred(Y), zero) :- isMinus(pred(X), pred(Y), succ(Z)).
isDiv(pred(X), pred(Y), succ(Z)) :- ','(isMinus(pred(X), pred(Y), A), isDiv(A, pred(Y), Z)).
isDiv(pred(X), succ(Y), Z) :- ','(isMinus(zero, pred(X), A), ','(isDiv(A, succ(Y), B), isMinus(zero, B, Z))).
isModulo(X, Y, Z) :- ','(isDiv(X, Y, A), ','(isTimes(A, Y, B), isMinus(X, B, Z))).
=(X, X).
succ(X) > zero.
succ(X) > pred(Y).
succ(X) > succ(Y) :- X > Y.
zero > pred(Y).
pred(X) > pred(Y) :- X > Y.
pred(X) < zero.
pred(X) < succ(Y).
pred(X) < pred(Y) :- X < Y.
zero < succ(Y).
succ(X) < succ(Y) :- X < Y.
