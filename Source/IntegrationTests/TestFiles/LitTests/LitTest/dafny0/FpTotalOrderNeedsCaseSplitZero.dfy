// RUN: %testDafnyForEachResolver "%s" -- --boogie /proverOpt:O:smt.case_split=0

// The order axioms that Dafny's DEFAULT solver options cannot discharge, pinned under the one
// option that changes the answer.
//
// Dafny's "<" on fp32/fp64 is a strict total order agreeing with "==" (see FpCoherentOrder.dfy for
// the definition and for the axioms that do go through by default). Totality, trichotomy and
// transitivity are true of it, and Z3 proves each of them from the SMT-LIB definition in hundredths
// of a second. Through Dafny none of them completes -- and neither does any stepping stone tried,
// including the raw IEEE disjunction the earlier partial order relied on.
//
// The cause is smt.case_split=3, which Dafny sets in DafnyOptions.ApplyDefaultOptions. Remove the
// option from the RUN line above and six of the seven lemmas below exhaust the resource limit
// (30-second timeouts under a plain "dafny verify"); with it, all seven verify in about a second.
// The difference is that setting and nothing else.
//
// This is the third floating-point incompleteness traced to that setting; the two conversion
// exactness checks in BoogieGenerator.Types.cs carry TODOs naming it as well, both saying the fix
// is either Z3's or a change to Dafny's solver configuration. Whether to select case_split=0 for
// programs that mention fp -- the way UseAbstractInterpretation is already switched off for them
// in BoogieGenerator -- is open. Until it is settled, the option lives here, so that the axioms
// are tested rather than merely asserted in a comment.

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

// Totality is what the partial order lacked, so it is worth stating on the values that used to be
// outside the order rather than only on quantified variables.
lemma TotalityReachesNaN(x: fp64) {
  assert x <= fp64.NaN || fp64.NaN <= x;
  assert x < fp64.NaN || x == fp64.NaN || fp64.NaN < x;
}
