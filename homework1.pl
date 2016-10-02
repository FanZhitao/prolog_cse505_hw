/* 1. prefix: Write a predicate prefix(L1,L2) that succeeds
   if and only if list L2 is a prefix of list L1: i.e. all 
   elements if L2 occur, in the same order, at the beginning
   of L1. N. */

prefix(_, []).
prefix([A|L1],[A|L2]) :-
	prefix(L1, L2).

/* 2. increasing: Write a predicate increasing(L) that, given
   a list L of integers, succeeds if and only if L is an 
   increasing sequence. That is, if x1 occurs before x2 in L,
   then x1 should be less than x2. */

increasing([_]).
increasing([A,B|L]) :-
	increasing([B|L]),
	A<B.

/* 3. pick_odd: Write an Prolog predicate pick_odd(L1, L2)
   that, given a list L1 returns in L2 the elements that occur
   at odd positions (i.e. 1,3,5,7,...) in L1. (Assume that the
   first element of a list is at position 1). */ 

pick_odd([], []).
pick_odd([A], [A]).
pick_odd([A,_|L1], [A|L2]) :-
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

and(P, Q) :-
	P,
	Q.

valid(T).

/* 7. nnf: Write a binary predicate nnf that, given a valid
   propositional boolean formula as its first argument, returns
   an equivalent formula in negation normal form (NNF). A
   formula is said to be in NNF if and only if in every
   subformula of the form not(t), t is a propositional variable. */

nnf().

/* 8. vars: Write a binary predicate vars that, given a valid
   propositional boolean formula as its first argument, returns
   (as its second argument) the set of variables in the formula.
   This returned set should be represented as a Prolog list,
   and should not have any duplicates (i.e. each variable
   appears once). */

/* 9. sat: Write a predicate sat(F), where F is a term
   representing a propositional boolean formula, that
	- succeeds, binding the propositional variables in F with
       a satisfying substitution if the formula is satisfiable.
	- fails, if the given formula is unsatisfiable. */

/* 10. Consider propositional boolean formulae from the previous
       question. Write a predicate tautology(F), where F is a
       term representing a boolean formula, that succeeds if and
       only if F is a tautology, i.e., true for every truth
       assignment to the propositional variables. */

/* 11. count: Write a binary predicate count(F, N) that, given
       a propositional boolean formula F, , binds N to the
       number of satisfying truth assignments to F. Note that
       if F is not satisfiable, N should be bound to 0; if F
       is a tautology, and F has k distinct propositional
       variables, then N should be bound to 2k. */
