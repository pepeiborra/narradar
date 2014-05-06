%query: goal(b,b,f)

% Generating a matrix of given dimensions with variables
% and subsequent instantiation of these variables.

goal(X,Y,Msu) :- s2m(X,Y,M), subs_mat(M,Msu).

s2m(0,Y,[]).
s2m(s(X),Y,[R|Rs]) :- s2l(Y,R), s2m(X,Y,Rs).

s2l(0,[]).
s2l(s(Y),[C|Cs]) :- s2l(Y,Cs).

subs_mat([],[]).
subs_mat([R|Rs],[SR|SRs]) :- subs_row(R,SR), subs_mat(Rs,SRs).

subs_row([],[]).
subs_row([E|R],[a|SR]) :- subs_row(R,SR).

