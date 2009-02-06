p(X,X).
p(f(X),g(Y)) :- p(f(X),f(Z)), p(Z,g(Y)).

%query: p(g,v)