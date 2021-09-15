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



member_clause(E, A):- n(B)=A, member_clause(E,B), !.
member_clause(E, A):- and(B,C)=A, member_clause(E,B), !.
member_clause(E, A):- and(B,C)=A, member_clause(E,C), !.
member_clause(E, A):- or(B,C)=A, member_clause(E,B), !.
member_clause(E, A):- or(B,C)=A, member_clause(E,C), !.
member_clause(E, A):- exists(X,F)=A, member_clause(E,X), !.
member_clause(E, A):- exists(X,F)=A, member_clause(E,F), !.
member_clause(E, A):- forevery(X,F)=A, member_clause(E,X), !.
member_clause(E, A):- forevery(X,F)=A, member_clause(E,F), !.
member_clause(E, A):- func(F,X)=A, member_clause(E,F), !.
member_clause(E, A):- func(F,X)=A, member_clause(E,X), !.
member_clause(E, A):- params(F,X)=A, member_clause(E,F), !.
member_clause(E, A):- params(F,X)=A, member_clause(E,X), !.
member_clause(E, A):- var(X)=A, member_clause(E,X), !.
member_clause(E, A):- const(X)=A, member_clause(E,X), !.
member_clause(E, E):- !.



rename_vars(A, D, V_LIST, n(R)):- n(B)=A, rename_vars(B, D, V_LIST, R), !.
rename_vars(A, D, V_LIST, and(R1, R2)):- and(B,C)=A, rename_vars(B, D, V_LIST, R1), rename_vars(C, D, V_LIST, R2), !.
rename_vars(A, D, V_LIST, or(R1, R2)):- or(B,C)=A, rename_vars(B, D, V_LIST, R1), rename_vars(C, D, V_LIST, R2), !.
rename_vars(A, D, V_LIST, R):- forevery(X,P)=A, generate_random_number(N), concat("x_", N, STRING), atom_string(V, STRING), put_dict(X,D,var(V),D_NEW), rename_vars(P, D_NEW, [var(V)|V_LIST], R), !.
rename_vars(A, D, V_LIST, R):- exists(X,P)=A, existential_quantifier(V_LIST, V), put_dict(X,D,V,D_NEW), rename_vars(P, D_NEW, V_LIST, R), !.
rename_vars(A, D, V_LIST, func(F,R)):- func(F,X)=A, rename_vars(X, D, V_LIST, R), !.
rename_vars(A, D, V_LIST, params(R1,R2)):- params(F,X)=A, rename_vars(F, D, V_LIST, R1), rename_vars(X, D, V_LIST, R2), !.
rename_vars(A, D, V_LIST, R):- get_dict(A, D, R), !.
rename_vars(A, D, V_LIST, const(A)):- !.

to_params([], _):-!, fail.
to_params([H|[]], H):-!.
to_params([H|T], params(H, R)):- to_params(T,R),!.

existential_quantifier(L, func(FNAME, PARAMS)):- length(L, LEN), LEN>0, generate_random_number(N), concat("y_", N, NAME), atom_string(FNAME,NAME), to_params(L, PARAMS), !.
existential_quantifier(L, const(FNAME)):- generate_random_number(N), concat("y_", N, NAME), atom_string(FNAME,NAME), !.
generate_random_number(R):- random(0,1000, R).

skolemize(A, R):- to_clause(A, C), rename_vars(C, t{}, [], R).

getArgs_as_List(A,[X|R]):- params(X,Y)=A, getArgs_as_List(Y,R), !.
getArgs_as_List(A,[A]):-!.

unify_vars(P,Q,[]):-const(A)=P, const(A)=Q, !.
unify_vars(P,Q,_):-const(A)=P, const(B)=Q, !, fail.
unify_vars(P,Q,[]):-var(A)=P, var(A)=Q, !.
unify_vars(P,Q,_):-var(A)=P, member_clause(P,Q), !, fail.
unify_vars(P,Q,[Q, P]):-var(A)=P, !.
unify_vars(P,Q,_):-var(A)=Q, member_clause(Q,P), !, fail.
unify_vars(P,Q,[P, Q]):-var(A)=Q, !.

unify_args([], [], []):-!.
unify_args([H1|T1], [H2|T2], R):-unify_func(H1,H2,R1), unify_args(T1,T2,R2), flatten(R1, R3), append(R3,R2,R), !.
unify_args([H1|T1], [H2|T2], R2):-unify_vars(H1,H2,R1), R1==[], unify_args(T1,T2,R2), !.
unify_args([H1|T1], [H2|T2], [R1|R2]):-unify_vars(H1,H2,R1), unify_args(T1,T2,R2), !.

unify_func(P,Q,R):- func(A,X)=P, func(A,Y)=Q, getArgs_as_List(X,ARG1), getArgs_as_List(Y,ARG2), length(ARG1,N), length(ARGS2, N), unify_args(ARG1, ARG2, R), !.



substitute_helper(F,S,C):-member([C,V], S), F==V,!.
substitute_helper(F,S,func(R1,R2)):-func(A,B)=F, substitute_helper(A,S,R1), substitute_helper(B,S,R2),!.
substitute_helper(F,S,params(R1,R2)):-params(A,B)=F, substitute_helper(A,S,R1), substitute_helper(B,S,R2),!.
substitute_helper(F,S,F):-!.


substitute([], S, []):-!.
substitute([H|T], S, [R1|R2]):- substitute_helper(H, S, R1), substitute(T,S,R2).
%substitute([H|T], S, [H|R]):- substitute(T, S, R).


formula_to_clause_helper(and(A,B), R):- formula_to_clause_helper(A,R1), formula_to_clause_helper(B,R2), append(R1,R2,R), !.
formula_to_clause_helper(or(A,B), [R]):- formula_to_clause_helper(A,R1), formula_to_clause_helper(B,R2), flatten(R1,R3), flatten(R2,R4), append(R3,R4,R), !. 
formula_to_clause_helper(A, [[A]]):-!.
formula_to_CNF_form(F,R):- to_clause(F,C), formula_to_clause_helper(C,R), !.


reduce_formulas_for_list([], []):-!.
reduce_formulas_for_list([H|T], [C|R]):- to_clause(H,C), reduce_formulas_for_list(T,R), !. 
clean_CNF([], []):-!.
clean_CNF([H|T], [L|R]):- reduce_formulas_for_list(H,C), list_to_set(C,L), clean_CNF(T, R), !.


apply_resolution_step(C, [R|C]):- member(C1, C), member(C2, C), C1 \= C2, member(func(P, X), C1), member(func(n(P), Y), C2), unify_func(func(P,X), func(P,Y), S), delete_elem(func(P,X), C1, C3), delete_elem(func(n(P), Y), C2, C4), substitute(C3, S, C5), substitute(C4, S, C6), merge_lists_no_duplicates(C5, C6, R), not(member(R, C)), !.
apply_resolution_step(C, [R|C]):- member(C1, C), member(C2, C), C1 \= C2, member(E, C1), to_clause(n(E), F1), member(F1,C2), delete_elem(E, C1, R1), delete_elem(F1, C2, R2), merge_lists_no_duplicates(R1, R2, R), not(member(R, C)), !.
apply_resolution_step(C, false):-!.


resolution_helper(CNF):- member([], CNF), !, fail.
resolution_helper(CNF):- apply_resolution_step(CNF, R), R \= false, resolution_helper(R), !.
resolution_helper(CNF):- apply_resolution_step(CNF, R), R == false, !.

convert_from_KB_to_formula([], []):-!.
convert_from_KB_to_formula([H|[]], H):-!.
convert_from_KB_to_formula([H|T], and(H,R)):- convert_from_KB_to_formula(T,R), !.

convert_from_KB_to_CNF(KB, R):- convert_from_KB_to_formula(KB, F), to_clause(F,C), skolemize(C,C_PRIME), formula_to_CNF_form(C_PRIME, R), !.


resolution_from_CNF(CNF):- clean_CNF(CNF, CNF_F), resolution_helper(CNF_F).
resolution_from_KB(KB, Q):- convert_from_KB_to_CNF([n(Q)|KB], CNF), resolution_from_CNF(CNF).


writeResults([]):-!.
writeResults([H|T]):- resolution_from_CNF(H), writeln(H), writeln("true"), writeln(""), writeResults(T), !.
writeResults([H|T]):- writeln(H), writeln("false"), writeln(""), writeResults(T), !.


read_file(S,[]) :- at_end_of_stream(S).
read_file(S,[L|R]) :- not(at_end_of_stream(S)), read(S,L), read_file(S,R).
main:- open('inputs_ex1.txt', read, S), read_file(S, L), writeResults(L), close(S).
