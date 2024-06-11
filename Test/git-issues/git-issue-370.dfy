// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Issue 370 reported a situation where there were 6 errors, but only 5 of
// them are reported, since there's a limit of 5 error messages per method.
// The confusing part was that the omitted error was the first of the 6,
// which makes it appear as if there's no problem with postcondition
// WellFormed(t) of foo(). While the ordering of error messages is not
// guaranteed to be deterministic, the current behavior for this test happens
// to be good, so this test file is meant to alert us to any changes, in
// case we then want to revisit this issue in some way.

datatype S = S(u: int, v: int, w: int, x: int, y: int, z: int)

predicate a(s: S)

predicate WellFormed(s: S) {
  && a(s)
}

predicate Good(s: S) {
  && s.u == 1
  && s.v == 2
  && s.w == 3
  && s.x == 4
  && s.y == 5
  && s.z == 6
}

function {:opaque} GetS(): S {
  S(1, 2, 3, 4, 5, 6)
}

lemma foo()
  ensures var s := GetS();
    WellFormed(s) && // error
    Good(s)  // error (6x, but only 4 of these are reported, due to the limit of 5 errors per method)
{
}