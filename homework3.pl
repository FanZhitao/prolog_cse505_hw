% SWI-Prolog Version 7.2.3.

/* 1. tpi/2: Given an integer i, tpi(i, f) is true if and only
   if an atomic formula f is in TPi({}). Recall that TP is the
   immediate consequence operator used for computing least
   Herbrand models, and TPi is the composition of i repeated
   applications of TP. */

tpi(0, []).
tpi(I, F) :-
    tpiSet(I, NewSet),
    subset0(NewSet, [F]).

% Helper functions

tpiSet(0, []).
tpiSet(1, Set) :-
    findall(F, pc(_, F, []), L),
    sort(L, Set).
tpiSet(I, Set) :-
    number(I),
    I > 1,
    I1 is I - 1,
    tpiSet(I1, PrevSet),
    findall(F, isTrue(F, PrevSet), L),
    append(PrevSet, L, TempL),
    set(TempL, TempSet),
    sort(TempSet, Set), !.

set([], []).
set([H|T], [H|Out]) :-
    not(member(H, T)),
    set(T, Out).
set([H|T], Out) :-
    member(H, T),
    set(T, Out).

subset0([], []).
subset0([E|Tail], [E|NTail]):-
    subset0(Tail, NTail).
subset0([_|Tail], NTail):-
    subset0(Tail, NTail).

isTrue(G, Set) :-
    pc(_, G, _),
    commalist_to_list(G, Gs),
    derive(Gs, Ds),
    delete(Ds, [], D),
    flatten(D, S),
    subset(S, Set).

flatten([], []) :- !.
flatten([L|Ls], FlatL) :-
    !,
    flatten(L, NewL),
    flatten(Ls, NewLs),
    append(NewL, NewLs, FlatL).
flatten(L, [L]).

derive([], []).
derive([G|Gs], [NGs|Ds]) :-
    pc(_, G, Bs),
    basics:append(Bs, Gs, NGs),
    derive(NGs, Ds).
   
print_derivation([]).
print_derivation([d(I,Gs)|Ds]) :-
    format('~~(~:d)~~> ', I),
    writeln(Gs),
    print_derivation(Ds).

interpret(G) :-
    commalist_to_list(G, Gs),
    derive(Gs, Ds),
    writeln(Gs),
    print_derivation(Ds).

/* 2. lm/1: When invoked with a ground atomic foruma f as its
   argument, this predicate succeeds if and only if f is in
   the least Herbrand model of the program.

   When invoked as lm(X), i.e., where X is a variable, this
   predicate should backtrack, binding X to every element in
   the least Herbrand model of the program.

   For this question, the evaluation of lm(X) should terminate
   after enumerating the least Herbrand model, if the loaded
   program is in Datalog (i.e. function-free). */

lm(F) :-
    hm(Set),
    subset0(Set, [F]).

hm(Set) :-
    hmHelper(0, Set).

hmHelper(I, Set) :-
    number(I),
    I1 is I + 1,
    tpiSet(I, S0),
    tpiSet(I1, S1),
    (S0 \= S1
    -> hmHelper(I1, Set)
    ;  Set = S0).

/* 3. lmi/1: When invoked as lm(N) where N is a variable,
   this predicates succeeds by binding N to the least number i
   such that, for every formmula f in the least Herbrand model
   of the program, tp(i, f) is true.

   In other words, lmi finds the number of iterations of TP
   needed to find the least Herbrand model of the program. */

lmi(N) :-
    lmiHelper(0, N).

lmiHelper(I, N) :-
    number(I),
    I1 is I + 1,
    tpiSet(I, S0),
    tpiSet(I1, S1),
    (S0 \= S1
    -> lmiHelper(I1, N)
    ;  N = I). 

/* 4. bfe/2: Invoked with a single goal literal g, bfe(g, N)
   should (1) bind variables in g such that it becomes the
   goal's computed answer, and (2) return in N the length of
   a successful derivation corresponding to the computed
   answer. For instance, let p(X) be a predicate defined in
   the program which has two computed answers p(a) and p(c),
   with derivations (respectively):

   p(X) ~> q(X,Y),r(X,Y),s(Y) ~> r(a,b), s(b) ~> []

   and

   p(X) ~> q(X,Y),t(X,Y) ~> t(c,d) ~> []

   Then bfe(p(X), N) should return (1) X=a and N=3 and
   (2) X=c and N=2 (upon backtracking). */

bfe(G, N) :-
    N1 is N - 1,
    tpi(N, G),
    not(tpi(N1, G)).

/* 5. Let f be a ground atomic formula and i be an integer
   such that tp(i, f) is false but tp(i+1, f) is true.

   Now consider the query bfe(f, N). What will be the set of
   possible bindings for N? Be as precise as possible and justify.
 */

% N is i+1.



% "Meta-Interpreter" for definite logic programs.
% Program to be interpreted is in a file, written in Prolog syntax.
% This progam is first loaded using load_pgm/1.
% Then a goal G is interpreted using interpret(G)
%    which computes answers for G
%    and prints out the derivations which result in the computed answer.

load_pgm(F) :-
	seeing(OF),
	see(F),
	initialize,
	read_and_load(0),
	seen,
	see(OF).

initialize :-
	retractall(pc(_,_,_)).

read_and_load(I) :-
	read(T),
	(T= end_of_file
	->  true
	;   (T = (H :- B)
	    ->  commalist_to_list(B, BL), assert(pc(I, H, BL))
	    ;	assert(pc(I, T, []))
	    ),
	    J is I+1,
	    read_and_load(J)
	).

commalist_to_list(CL, L) :-
	phrase(commalist_to_list(CL), L).
	
commalist_to_list((C1,C2)) --> !, commalist_to_list(C1), commalist_to_list(C2).
commalist_to_list(C) --> [C].
/*
derive([], []).
derive([G|Gs], [d(I,NGs)|Ds]) :-
	pc(I, G, Bs),
	basics:append(Bs, Gs, NGs),
	derive(NGs, Ds).
	
print_derivation([]).
print_derivation([d(I,Gs)|Ds]) :-
	format('~~(~:d)~~> ', I),
	writeln(Gs),
	print_derivation(Ds).

interpret(G) :-
	commalist_to_list(G, Gs),
	derive(Gs, Ds),
	writeln(Gs),
	print_derivation(Ds).
*/
% The canonical 3-line meta interpreter for definite programs.
interp(true) :- !.
interp((G1,G2)) :- !, interp(G1), interp(G2).
interp(G) :- clause(G, B), interp(B).