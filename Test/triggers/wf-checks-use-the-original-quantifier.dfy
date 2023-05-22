// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test checks that typical expressions requiring WF checks do not suddenly
// loose expressivity due to quantifier splitting. Without special care, the
// expression (forall x :: x != null && x.a == 0) could fail to verify.

// The logic about split quantifiers is that Boogie (and z3) should never realize
// that there was an unsplit quantifier. The WF check code does not produce a
// quantifier, at least in it's checking part; thus, it should use original
// quantifier. This fixes a problem in VerifyThis2015/Problem2.dfy with a null
// check, and a problem spotted by Chris, made into a test case saved in
// triggers/wf-checks-use-the-original-quantifier.dfy.

// Of course, the assumption that WF checks produce for a quantifier is a
// quantifier, so the assumption part that comes after the WF check does use the
// split expression.

// This test case is inspired by the example that Chris gave.

ghost predicate P(b: nat)
ghost function f(a: int): int
class C { var x: int; }

method M(s: set<C>)
  requires forall n: nat :: 0 <= f(n) && P(f(n))
  requires forall c, c' | c in s && c' in s :: c.x == c'.x {
}
