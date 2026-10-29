// RUN: %testDafnyForEachResolver "%s" -- --boogie /proverOpt:O:smt.case_split=0

// The order axioms that Dafny's DEFAULT solver options cannot discharge, pinned under the one
// option that changes the answer.
//
// Dafny's "<" on fp32/fp64 is a strict total order agreeing with "==" (FpCoherentOrder.dfy has the
// definition and the axioms that go through by default). Totality, trichotomy and transitivity hold
// too, and Z3 proves each from the SMT-LIB definition in hundredths of a second, but none completes
// through Dafny, nor does any user-level stepping stone.
//
// The cause is smt.case_split=3, set in DafnyOptions.ApplyDefaultOptions. Remove the option from the
// RUN line and most of the lemmas below exhaust the resource limit; with it, all verify in about a
// second. That setting is the difference and nothing else.
//
// The third fp incompleteness traced to it; the conversion exactness checks in
// BoogieGenerator.Types.cs carry TODOs for the other two. Whether to select case_split=0 for
// programs mentioning fp -- as UseAbstractInterpretation is already switched off for them -- is
// open. Until then the option lives here, so the axioms are tested rather than asserted in prose.

lemma Totality(a: fp64, b: fp64) {
  assert a <= b || b <= a;
}

lemma Trichotomy(a: fp64, b: fp64) {
  assert a < b || a == b || b < a;
  // Exactly one of the three, which is what makes "<" agree with "==" rather than merely coexist.
  assert a < b ==> !(a == b) && !(b < a);
  assert a == b ==> !(a < b) && !(b < a);
}

lemma Transitivity(a: fp64, b: fp64, c: fp64) {
  assert a < b && b < c ==> a < c;
  assert a <= b && b <= c ==> a <= c;
}

lemma TotalityFp32(a: fp32, b: fp32) {
  assert a <= b || b <= a;
}

lemma TrichotomyFp32(a: fp32, b: fp32) {
  assert a < b || a == b || b < a;
}

lemma TransitivityFp32(a: fp32, b: fp32, c: fp32) {
  assert a < b && b < c ==> a < c;
}

// Totality stated on NaN itself, not only on quantified variables.
lemma TotalityReachesNaN(x: fp64) {
  assert x <= fp64.NaN || fp64.NaN <= x;
  assert x < fp64.NaN || x == fp64.NaN || fp64.NaN < x;
}

// The order's minimum and maximum, one line each, for when IEEE fp.min/fp.max are not what is wanted
// (FpCoherentOrder.dfy says when that is). Being bounds needs no non-NaN hypothesis, which is the
// benefit: totality is what makes an order-based min total.
function OrderMin(x: fp64, y: fp64): fp64 { if x < y then x else y }
function OrderMax(x: fp64, y: fp64): fp64 { if x < y then y else x }

lemma TheOrdersMinAndMaxAreBounds(x: fp64, y: fp64) {
  assert OrderMin(x, y) <= x && OrderMin(x, y) <= y;
  assert x <= OrderMax(x, y) && y <= OrderMax(x, y);
  assert OrderMin(x, y) == x || OrderMin(x, y) == y;
  assert OrderMax(x, y) == x || OrderMax(x, y) == y;
}

// Totality makes "<=" the complement of the reversed "<". That is how the compiled "<=" is defined,
// and it is why the translator does NOT define FpAtMost that way: doing so turns antisymmetry into
// trichotomy, which is on this file's side of the line.
lemma AtMostIsTheComplementOfReversedLess(a: fp64, b: fp64) {
  assert (a <= b) == !(b < a);
  assert (a >= b) == !(a < b);
}
