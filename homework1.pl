% SWI-Prolog Version 7.3.27.

/* 1. prefix: Write a predicate prefix(L1,L2) that succeeds
   if and only if list L2 is a prefix of list L1: i.e. all 
   elements if L2 occur, in the same order, at the beginning
   of L1. N. */

prefix(_, []).
prefix([A|L1], [A|L2]) :-
	prefix(L1, L2).

/* 2. increasing: Write a predicate increasing(L) that, given
   a list L of integers, succeeds if and only if L is an 
   increasing sequence. That is, if x1 occurs before x2 in L,
   then x1 should be less than x2. */

increasing([_]) :- true, !.
increasing([A, B|L]) :-
	increasing([B|L]),
	A < B.

/* 3. pick_odd: Write an Prolog predicate pick_odd(L1, L2)
   that, given a list L1 returns in L2 the elements that occur
   at odd positions (i.e. 1,3,5,7,...) in L1. (Assume that the
   first element of a list is at position 1). */ 

pick_odd([], []) :- true, !.
pick_odd([A], [A]) :- true, !.
pick_odd([A, _|L1], [A|L2]) :-
	pick_odd(L1, L2).

/* 4. increasing_subsequence: Write a Prolog predicate incsub
   such that, given a list of integers L1, incsub(L1, L2)
   returns in L2 an increasing subsequence of L1. (You may
   assume that L1 contains distinct elements). */

incsub(_, []).
incsub([H|T1], [H|T2]) :-
	incsub(T1, T2),
	increasing([H|T2]).
incsub([_|T1], T2) :-
	incsub(T1, T2),
	increasing(T2).

/* 5. factor: Write a predicate factor(N, I) that, given a
   positive integer N returns a factor of N in I. The
   predicate should list all factors of N upon backtracking,
   failing finally when all factors have been returned. */

factor(X, Y) :-
	between(1, X, Y),
	integer(X),
	integer(Y),
	X mod Y =:= 0.

/* 6. valid: Write a unary predicate valid that, given a term T,
   succeeds if and only if T represents a valid propositional
   boolean formula.*/

is_true(true).
is_true(A) :-
	var(A), !, fail.
is_true(and(A, B)) :-
	and(A, B).
is_true(or(A, B)) :-
	or(A, B).
is_true(not(A)) :-
	is_false(A).

is_false(false).
is_false(A) :-
	var(A), !, fail.
is_false(and(A, B)) :-
	notand(A, B).
is_false(or(A, B)) :-
	notor(A, B).
is_false(not(A)) :-
	is_true(A).

not(false) :- true, !.
not(A) :-
	is_false(A).

and(A, B) :-
	is_true(A),
	is_true(B).

or(A, B) :-
	is_true(A);
	is_true(B).

notand(A, B) :-
	is_false(A);
	is_false(B).

notor(A, B) :-
	is_false(A),
	is_false(B).

valid(Variable) :-
	var(Variable), !.
valid(true) :- true, !.
valid(false) :- true, !.
valid(not(Formula)) :-
	valid(Formula), !.
valid(and(Formula1, Formula2)) :-
	valid(Formula1),
	valid(Formula2), !.
valid(or(Formula1, Formula2)) :-
	valid(Formula1),
	valid(Formula2).

/* 7. nnf: Write a binary predicate nnf that, given a valid
   propositional boolean formula as its first argument, returns
   an equivalent formula in negation normal form (NNF). A
   formula is said to be in NNF if and only if in every
   subformula of the form not(t), t is a propositional variable. */

isnnf(Formula) :-
	var(Formula), !.
isnnf(not(Formula)) :-
	var(Formula), !.
isnnf(and(Formula1, Formula2)) :-
	isnnf(Formula1),
	isnnf(Formula2), !.
isnnf(or(Formula1, Formula2)) :-
	isnnf(Formula1),
	isnnf(Formula2), !.
isnnf(true) :- true, !.
isnnf(false).

nnf(Formula, Formula) :-
	isnnf(Formula), !.
nnf(not(not(Formula)), NNF) :-
	nnf(Formula, NNF).
nnf(not(and(Formula1, Formula2)), NNF) :-
	nnf(or(not(Formula1), not(Formula2)), NNF).
nnf(not(or(Formula1, Formula2)), NNF) :-
	nnf(and(not(Formula1), not(Formula2)), NNF).

/* 8. vars: Write a binary predicate vars that, given a valid
   propositional boolean formula as its first argument, returns
   (as its second argument) the set of variables in the formula.
   This returned set should be represented as a Prolog list,
   and should not have any duplicates (i.e. each variable
   appears once). */

vars(Variable, [Variable]) :-
	var(Variable), !.
vars(not(Formula), List) :-
	vars(Formula, List).
vars(and(Formula1, Formula2), List) :-
	vars(Formula1, List1),
	vars(Formula2, List2),
	append(List1, List2, List3),
	sort(List3, List).
vars(or(Formula1, Formula2), List) :-
	vars(Formula1, List1),
	vars(Formula2, List2),
	append(List1, List2, List3),
	sort(List3, List).
vars(true, []) :- true, !.
vars(false, []).

/* 9. sat: Write a predicate sat(F), where F is a term
   representing a propositional boolean formula, that
	- succeeds, binding the propositional variables in F with
       a satisfying substitution if the formula is satisfiable.
	- fails, if the given formula is unsatisfiable. */

bind([], []).
bind([_|T1], [true|T2]) :-
	bind(T1, T2).
bind([_|T1], [false|T2]) :-
	bind(T1, T2).

isTrueCut(Formula) :-
	Formula, !.

sat(Formula) :-
	valid(Formula),
	vars(Formula, Vars),
	bind(Vars, Binding),
	Vars = Binding,
	isTrueCut(Formula).

/* 10. Consider propositional boolean formulae from the previous
       question. Write a predicate tautology(F), where F is a
       term representing a boolean formula, that succeeds if and
       only if F is a tautology, i.e., true for every truth
       assignment to the propositional variables. */

/*
tautology(Variable) :-
	var(Variable), !, fail.
tautology(or(Formula, Formula)) :-
	tautology(Formula), !.
tautology(and(Formula, Formula)) :- 
	tautology(Formula), !.
tautology(or(Formula, not(Formula))) :- true, !.
tautology(or(not(Formula), Formula)) :- true, !.
tautology(true).
tautology(Formula) :-
	nnf(Formula, NNF),
	(NNF = and(or(P, Q), or(not(P), R));
	NNF = and(or(not(P), R), or(P, Q));
	NNF = and(or(Q, P), or(R, not(P)));
	NNF = and(or(R, not(P)), or(Q, P))),
	tautology(or(Q, R)), !.
*/

tautology(Formula) :-
	\+ is_true(not(Formula)).

/* 11. count: Write a binary predicate count(F, N) that, given
       a propositional boolean formula F, , binds N to the
       number of satisfying truth assignments to F. Note that
       if F is not satisfiable, N should be bound to 0; if F
       is a tautology, and F has k distinct propositional
       variables, then N should be bound to 2k. */

count(Formula, N) :-
	vars(Formula, Vars),
	findall(Vars, sat(Formula), List),
	length(List, N).
