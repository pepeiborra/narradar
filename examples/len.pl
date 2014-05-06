%query: len(i,o)
len([],0).
len([A|B],s(X)) :- len(B,X).