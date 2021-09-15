member(E,[E|_]).
member(E,[_|T]):-member(E,T).

delete_elem(E, [], []):-!.
delete_elem(E, [E|T], R):- delete_elem(E, T, R), !.
delete_elem(E, [H|T], [H|R]):- delete_elem(E, T, R), !.

merge_lists_no_duplicates(L1, L2, R):- append(L1,L2,R1), list_to_set(R1, R).

to_clause(A, R):- and(B,B)=A, to_clause(B, R), !.
to_clause(A, R):- or(B,B)=A, to_clause(B, R), !. 
to_clause(A, R):- n(n(B))=A, to_clause(B, R),!.

to_clause(A, R):- n(and(B,C))=A, to_clause(n(B), R1), to_clause(n(C), R2), to_clause(or(R1, R2), R), !.
to_clause(A, R):- n(or(B,C))=A, to_clause(n(B), R1), to_clause(n(C), R2), to_clause(and(R1, R2), R), !.
to_clause(A, R):- n(forevery(X,F))=A, to_clause(n(F),R1), to_clause(exists(X, R1), R), !.
to_clause(A, R):- n(exists(X,F))=A, to_clause(n(F),R1), to_clause(forevery(X, R1), R), !.
to_clause(A, R):- n(func(B,X))=A, to_clause(n(B),R1), to_clause(func(R1, X), R), !.
to_clause(A, n(R)):- n(B)=A, to_clause(B,R), R == B, !.
to_clause(A, R):- n(B)=A, to_clause(B,R1), to_clause(n(R1), R), !.

to_clause(A, R):-equivalent(B,C)=A, to_clause(n(B), R1), to_clause(C, R2), to_clause(B, R3), to_clause(n(C), R4), to_clause(and(or(R1, R2), or(R3, R4)), R), !.
to_clause(A, R):-inclusion(B,C)=A, to_clause(n(B), R1), to_clause(C, R2), to_clause(or(R1, R2), R), !.

to_clause(A,forevery(X,R)):-and(B,forevery(X, C))=A, not(member_clause(X,B)), to_clause(and(B,C), R), !.
to_clause(A, and(R1,R2)):- and(B,C)=A, to_clause(B,R1), to_clause(C,R2), R1 == B, R2 == C,!.
to_clause(A, R):- and(B,C)=A, to_clause(B,R1), to_clause(C,R2), to_clause(and(R1,R2), R),!.

to_clause(A, R):- or(B, and(C,D))=A, to_clause(B, R1), to_clause(C,R2), to_clause(D,R3), to_clause(and(or(R1,R2), or(R1,R3)), R), !.
to_clause(A, R):- or(and(C,D), B)=A, to_clause(B, R1), to_clause(C,R2), to_clause(D,R3), to_clause(and(or(R1,R2), or(R1,R3)), R), !.
to_clause(A,forevery(X,R)):-or(B,forevery(X, C))=A, not(member_clause(X,B)), to_clause(or(B,C), R), !. 
to_clause(A, or(R1,R2)):- or(B,C)=A, to_clause(B,R1), to_clause(C,R2), R1 == B, R2 == C, !.
to_clause(A, R):- or(B,C)=A, to_clause(B,R1), to_clause(C,R2), to_clause(or(R1,R2), R),!.


to_clause(A, func(R1,R2)):- func(B,X)=A, to_clause(B,R1), to_clause(X,R2), R1 == B, R2 == X, !.
to_clause(A, R):- func(B,X)=A, to_clause(B,R1), to_clause(X,R2), to_clause(func(R1, R2), R), !.
to_clause(A, forevery(X,R)):- forevery(X, F)=A, to_clause(F, R), !.
to_clause(A, exists(X,R)):- exists(X, F)=A, to_clause(F, R), !.
to_clause(A, A):-!.


formula_to_clause_helper(and(A,B), R):- formula_to_clause_helper(A,R1), formula_to_clause_helper(B,R2), append(R1,R2,R), !.
formula_to_clause_helper(or(A,B), [R]):- formula_to_clause_helper(A,R1), formula_to_clause_helper(B,R2), flatten(R1,R3), flatten(R2,R4), append(R3,R4,R), !. 
formula_to_clause_helper(A, [[A]]):-!.
formula_to_CNF_form(F,R):- to_clause(F,C), formula_to_clause_helper(C,R),!.


count_no_appereance_elem_list([], E, 0):-!.
count_no_appereance_elem_list([E|T], E, N):- count_no_appereance_elem_list(T,E,N1), N is N1+1, !.
count_no_appereance_elem_list([_|T], E, N):- count_no_appereance_elem_list(T,E,N), !.


getFrequency_vars_helper([], L, []):-!.
getFrequency_vars_helper([H|T], L, [[H,NO]|R]):- count_no_appereance_elem_list(L,H,NO), getFrequency_vars_helper(T,L,R),!.
getFrequency_vars(C, R):- flatten(C,L), list_to_set(L,SET), getFrequency_vars_helper(SET,L,R), !.


getMaxElem([], false):-!, fail.
getMaxElem([[E,NO]|[]], [E,NO]):-!.
getMaxElem([[E,NO]|H], [E1,NO1]):- getMaxElem(H,[E1,NO1]), NO1>NO, !.
getMaxElem([[E,NO]|H], [E,NO]):-!.
getMaxAppearanceAtom([], A):-!, fail.
getMaxAppearanceAtom(CNF, A):- clean_CNF(CNF, CNF_F), getFrequency_vars(CNF_F, R), getMaxElem(R, [A,_]), !.


getMinElem([], false):-!, fail.
getMinElem([[E,NO]|[]], [E,NO]):-!.
getMinElem([[E,NO]|H], [E1,NO1]):- getMinElem(H,[E1,NO1]), NO1<NO, !.
getMinElem([[E,NO]|H], [E,NO]):-!.
getMinAppearanceAtom([], A):-!, fail.
getMinAppearanceAtom(CNF, A):- clean_CNF(CNF, CNF_F), getFrequency_vars(CNF_F, R), getMinElem(R, [A,_]), !.


special_prod([], A, []):-!.
special_prod([C|T], A, [C|R]):- to_clause(A, R1), to_clause(n(A), R2), not(member(R1, C)), not(member(R2, C)), special_prod(T, A, R), !.
special_prod([C|T], A, [C1|R]):- to_clause(A, R1), to_clause(n(A), R2), not(member(R1, C)), member(R2, C), special_prod(T, A, R), delete_elem(R2, C, C1), !.
special_prod([C|T], A, R):- special_prod(T,A,R), !.


reduce_formulas_for_list([], []):-!.
reduce_formulas_for_list([H|T], [C|R]):- to_clause(H,C), reduce_formulas_for_list(T,R), !. 
clean_CNF([], []):-!.
clean_CNF([H|T], [L|R]):- reduce_formulas_for_list(H,C), list_to_set(C,L), clean_CNF(T, R), !.


convert_from_KB_to_CNF([], []):-!.
convert_from_KB_to_CNF([H|T], R):- convert_from_KB_to_CNF(T,R1), formula_to_CNF_form(H,C), append(C, R1, R), !.


dp_MaxAppearanceAtom_helper([], []):-!.
dp_MaxAppearanceAtom_helper(C, R):- member([], C), !, fail.
dp_MaxAppearanceAtom_helper(C, [[A/true]|R]):- getMaxAppearanceAtom(C,A), special_prod(C,A,C1), dp_MaxAppearanceAtom_helper(C1, R), !.
dp_MaxAppearanceAtom_helper(C, [[A/false]|R]):- getMaxAppearanceAtom(C,A), to_clause(n(A), F), special_prod(C,F,C1), dp_MaxAppearanceAtom_helper(C1, R), !.
dp_MaxAppearanceAtom(CNF, R):- clean_CNF(CNF, CNF_F), dp_MaxAppearanceAtom_helper(CNF_F, R).


dp_MinAppearanceAtom_helper([], []):-!.
dp_MinAppearanceAtom_helper(C, R):- member([], C), !, fail.
dp_MinAppearanceAtom_helper(C, [[A/true]|R]):- getMinAppearanceAtom(C,A), special_prod(C,A,C1), dp_MinAppearanceAtom_helper(C1, R), !.
dp_MinAppearanceAtom_helper(C, [[A/false]|R]):- getMinAppearanceAtom(C,A), to_clause(n(A), F), special_prod(C,F,C1), dp_MinAppearanceAtom_helper(C1, R), !.
dp_MinAppearanceAtom(CNF, R):- clean_CNF(CNF, CNF_F), flatten(CNF_F,L), list_to_set(L,SET), dp_MinAppearanceAtom_helper(CNF_F, R).



writeResults([]):-!.
writeResults([H|T]):- dp_MinAppearanceAtom(H,R1), dp_MaxAppearanceAtom(H,R2), writeln(H), write("min app: "), writeln(R1),  write("max app: "), writeln(R2), writeln(""), writeResults(T), !.
writeResults([H|T]):- writeln(H), writeln("min app-> false"), writeln("max app-> false"), writeln(""), writeResults(T), !.


read_file(S,[]) :- at_end_of_stream(S).
read_file(S,[L|R]) :- not(at_end_of_stream(S)), read(S,L), read_file(S,R).
main:- open('inputs_ex2.txt', read, S), read_file(S, L), writeResults(L), close(S).



