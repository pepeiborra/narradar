%query: p(f).
p(X) :- q(f(X)).
q(X) :- r(X,Y), q(Y).
r(f(s(s(X))),f(s(X))).