append([],L,L).
append([X|Xs],Ys,[X|Zs]) :- append(Xs,Ys,Zs).
rotate(N,O) :- append(L,M,N), append(M,L,O).
%query: rotate(g,v).
