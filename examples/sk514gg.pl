nat(zero).  
nat(s(X)) :- nat(X).
inv(neg(X), pos(X)).
inv(pos(X), neg(X)).
safeinv(X, neg(Y)) :- inv(X, neg(Y )), nat(Y ).
safeinv(X, pos(Y)) :- inv(X, pos(Y )), nat(Y ).

%query: safeinv(g,g)