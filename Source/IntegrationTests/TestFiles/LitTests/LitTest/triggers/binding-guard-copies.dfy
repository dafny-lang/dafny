// RUN: %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A substitution gives its copy of a binding guard a type, and lets the statements that the guard guards use the copy's
// variables

predicate A(x: int) { x % 2 == 0 }
predicate P(x: int)
predicate Q<T(!new)>(y: T)

function Guarded(n: int): int
  requires (assert true by { if x :| A(x) { } if case x :| A(x) => case true => } n >= 0)
{
  0
}

// {:autoReq} copies the guards, which need a type
function {:autoReq} CallsGuarded(n: int): int {
  Guarded(n)
}

lemma GuardedLemma(n: int)
  ensures (assert true by { if x :| A(x) { } } P(n) || !P(n))
{
}

// And so does the forall statement's copy of the lemma's postcondition
method CallsGuardedLemma() {
  forall n | 0 <= n < 3 {
    GuardedLemma(n);
  }
}

function GuardedGeneric<T(!new)>(t: T): int
  requires (assert true by { if y: T :| Q(y) { assert Q(y); } if case y: T :| Q(y) => assert Q(y); case true => } true)
{
  0
}

// The copy of each guard has a y of type int, which the statement that the guard guards uses too
function {:autoReq} CallsGuardedGeneric(n: int): int {
  GuardedGeneric(n)
}
