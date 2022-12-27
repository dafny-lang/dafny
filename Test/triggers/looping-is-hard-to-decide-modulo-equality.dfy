// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows cases where loops could hide behind equalities. In all three
// cases we behave the same; that is, we don't warn for loops that would only
// exist in the presence of an equality. The easiest way to understand the
// issue, I (CPC) feel, is to look at the old case: f(x) could very well loop
// with old(f(f(x))) if f(f(x)) did not change the heap at all.

// This equality issue is generally undecidable. It could make sense to special
// case `old`, but KRML and CPC decided against it on 2015-08-21. Future
// experiences could cause a change of mind.

class C { }
function f(c: C): C reads c
function g(c: C): C
function h(c: C, i: int): C

// With explicit arguments
method M0(i: int, j: int, sc: set<C>) {
  assert forall c | c in sc :: true || h(c, i) == h(h(c, j), j);
}

// With implicit arguments (f and g respectively, to Apply)
method M1(f: int -> int, g: int -> int) {
  assert forall x :: true || f(x) == g(f(x));
}

// With implicit arguments (the heap, to old)
method M2(sc: set<C>) {
  assert forall c | c in sc :: true || f(c) == old(f(f(c)));
}
