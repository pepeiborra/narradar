
goal(X) :- f([],L), pl(L), insert(s(0), [0,s(s(0))|X], L1), g(L1).

f(Y,L) :- insert(s(0), [0|Y], L).

pl([]).
pl([0|Y]) :- pl(Y).
pl([s(X)|Y]) :- pl([X|Y]).

g(X) :- insert(_,[],L) , g(X).

insert(X,[],[X]).
insert(X,[X1|L],[X1,X|Y]).