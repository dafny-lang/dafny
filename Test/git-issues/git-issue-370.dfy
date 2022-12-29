// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Issue 370 reported a situation where there were 6 errors, but only 5 of
// them are reported, since there's a limit of 5 error messages per method.
// The confusing part was that the omitted error was the first of the 6,
// which makes it appear as if there's no problem with postcondition
// WellFormed(t) of foo(). While the ordering of error messages is not
// guaranteed to be deterministic, the current behavior for this test happens
// to be good, so this test file is meant to alert us to any changes, in
// case we then want to revisit this issue in some way.

datatype T = T(x: int)
datatype S = S(u: int, v: int, w: int, x: int, y: int, z: int)

predicate a(t: T)

predicate WellFormed(t: T) {
  && a(t)
}

function Func(t: T): S
  requires WellFormed(t)  // Note, there should be NO complaint about this precondition in foo() below.
{
  S(t.x, t.x, t.x, t.x, t.x, t.x)
}

predicate Good(s: S) {
  && s.u == 5
  && s.v == 5
  && s.w == 5
  && s.x == 5
  && s.y == 5
  && s.z == 5
}

function {:opaque} GetT(): T {
  T(5)
}

lemma foo()
  ensures var t := GetT();
    && WellFormed(t)  // error (1x)
    && Good(Func(t))  // error (5x, but only 4 of these are reported, due to the limit of 5 errors per method)
{
  reveal GetT();
}
