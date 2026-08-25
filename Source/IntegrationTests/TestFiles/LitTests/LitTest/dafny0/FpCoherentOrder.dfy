// RUN: %testDafnyForEachResolver "%s"

// Dafny's "==" on floating point is structural equality on the SMT FloatingPoint sort, which
// keeps -0.0 and +0.0 apart. Raw IEEE fp.lt leaves them tied, and the combination was incoherent:
// trichotomy failed and "a <= b && b <= a ==> a == b" was refutable. "<" is now fp.lt refined so
// that -0.0 < +0.0 -- which is IEEE 754-2019 clause 5.10 totalOrder restricted to non-NaN -- so
// "==" and "<" come from one order instead of two incompatible ones.
//
// NaN stays outside the order: comparison carries an unconditional non-NaN obligation, and
// totalOrder would additionally distinguish NaN signs and payloads, which this encoding, having
// exactly one NaN value, does not model.

lemma SignedZerosAreOrdered() {
  var p: fp64 := 0.0;
  var n: fp64 := -0.0;
  assert n != p;          // structural equality keeps them apart
  assert n < p;           // ... and the order now agrees
  assert n <= p;
  assert p > n;
  assert p >= n;
  assert !(p < n);
  assert !(p <= n);
}

lemma SignedZerosAreOrderedFp32() {
  var p: fp32 := 0.0;
  var n: fp32 := -0.0;
  assert n != p && n < p && n <= p && p > n && p >= n;
}

// Antisymmetry: this was refutable under raw fp.lt.
lemma Antisymmetry(a: fp64, b: fp64)
  requires !a.IsNaN && !b.IsNaN
{
  assert a <= b && b <= a ==> a == b;
}

lemma AntisymmetryFp32(a: fp32, b: fp32)
  requires !a.IsNaN && !b.IsNaN
{
  assert a <= b && b <= a ==> a == b;
}

// The unchecked static methods keep raw IEEE comparison, which leaves the two zeros tied. This
// mirrors fp*.Equal keeping IEEE equality while "==" is value identity: the static-method family
// is the IEEE view, the operators are Dafny's.
lemma UncheckedMethodsStayIeee() {
  var p: fp64 := 0.0;
  var n: fp64 := -0.0;
  assert n < p;                     // operator: ordered
  assert !fp64.Less(n, p);          // method: IEEE leaves them tied
  assert !fp64.Less(p, n);
  assert fp64.LessOrEqual(p, n);    // IEEE: +0.0 <= -0.0 holds
  assert !(p <= n);                 // operator: it does not
  assert fp64.Equal(p, n);          // IEEE equality identifies them
  assert p != n;                    // value identity does not
}

// Ordinary comparisons are unaffected.
lemma OrdinaryValues() {
  var one: fp64 := 1.0;
  var two: fp64 := 2.0;
  assert one < two && one <= two && two > one && two >= one;
  assert !(two < one);
  var negOne: fp64 := -1.0;
  assert negOne < one && negOne < 0.0 && 0.0 < one;
}

// Totality and trichotomy hold of the order, but Z3 does not discharge them from the refined
// definition unaided: "assert a <= b || b <= a" under these preconditions times out past a minute.
// Establishing the IEEE disjunction first is enough, because the refinement only adds the pair of
// zeros, and once the solver has the IEEE case split it can finish. This is worth pinning both ways
// round: the properties are real, and the stepping stone is what a user will need.
lemma TotalityNeedsTheIeeeSteppingStone(a: fp64, b: fp64)
  requires !a.IsNaN && !b.IsNaN
{
  assert fp64.LessOrEqual(a, b) || fp64.LessOrEqual(b, a);
  assert a <= b || b <= a;
}

lemma TrichotomyNeedsTheIeeeSteppingStone(a: fp64, b: fp64)
  requires !a.IsNaN && !b.IsNaN
{
  assert fp64.Less(a, b) || fp64.Equal(a, b) || fp64.Less(b, a);
  assert a < b || a == b || b < a;
}

lemma AntisymmetryHolds(a: fp64, b: fp64)
  requires !a.IsNaN && !b.IsNaN
  requires a <= b && b <= a
  ensures a == b
{
}
