p(X) :- q(f(Y)),p(Y).
p(g(X)) :- p(X).
q(g(Y)).

%query: p(g)