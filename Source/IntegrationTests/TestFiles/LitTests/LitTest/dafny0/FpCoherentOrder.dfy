// RUN: %testDafnyForEachResolver "%s"

// Dafny's "<" on floating point is a strict total order on the whole domain that agrees with "==".
// Two refinements of IEEE fp.lt get it there.
//
// -0.0 < 0.0, because "==" is structural equality on the SMT FloatingPoint sort, which keeps the
// two zeros apart while raw fp.lt leaves them tied. The combination was incoherent: trichotomy
// failed and "a <= b && b <= a ==> a == b" was refutable. IEEE 754-2019 clause 5.10 totalOrder
// specifies which way to break the tie.
//
// NaN is above every number, which makes the order total rather than partial and is why comparison
// carries no non-NaN obligation while arithmetic does: a comparison yields a bool, so there is no
// unrequested NaN for an obligation to prevent. totalOrder does not settle where NaN goes, since it
// splits NaNs by sign across both ends and this encoding has exactly one NaN; the top follows
// java.lang.Double.compare.
//
// This file holds what a user can prove under Dafny's default solver options. Totality,
// trichotomy and transitivity are also true, but need a different option to discharge -- see
// FpTotalOrderNeedsCaseSplitZero.dfy, which says why.

lemma SignedZerosAreOrdered() {
  var p: fp64 := 0.0;
  var n: fp64 := -0.0;
  assert n != p;          // structural equality keeps them apart
  assert n < p;           // ... and the order agrees
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

// NaN is the maximum. Note the absence of any precondition on the comparisons themselves: what
// needs !x.IsNaN here is the CONCLUSION x < NaN, not the well-formedness of writing it.
lemma NaNIsTheMaximum(x: fp64)
  requires !x.IsNaN
{
  assert x < fp64.NaN;
  assert x <= fp64.NaN;
  assert !(fp64.NaN < x);
  assert !(fp64.NaN <= x);
  assert fp64.PositiveInfinity < fp64.NaN;   // above the infinities too
}

lemma NaNIsTheMaximumFp32(x: fp32)
  requires !x.IsNaN
{
  assert x < fp32.NaN && !(fp32.NaN < x);
}

// Strict at NaN, and "<=" reflexive there, because "==" is: the sort has exactly one NaN.
lemma NaNIsNotBelowItself(x: fp64, y: fp64)
  requires x.IsNaN && y.IsNaN
{
  assert x == y;
  assert !(x < y);
  assert x <= y;
}

// Comparing possibly-NaN operands is well formed. Before the order was made total this method was
// four errors.
lemma ComparisonHasNoNaNObligation(x: fp64, y: fp64) {
  var a := x < y;
  var b := x <= y;
  var c := x > y;
  var d := x >= y;
  assert a == (y > x);
  assert b == (y >= x);
}

// Antisymmetry, which was refutable under raw fp.lt, and now needs no hypothesis at all.
lemma Antisymmetry(a: fp64, b: fp64) {
  assert a <= b && b <= a ==> a == b;
}

lemma AntisymmetryFp32(a: fp32, b: fp32) {
  assert a <= b && b <= a ==> a == b;
}

lemma AntisymmetryHolds(a: fp64, b: fp64)
  requires a <= b && b <= a
  ensures a == b
{
}

// "<=" is the reflexive closure of "<", and "<" is irreflexive -- again unconditionally. Both
// directions matter: "<" and "<=" have separate definitions in the translator, and this is what
// pins them to the same order. FpTotalOrderNeedsCaseSplitZero.dfy adds the identity that only
// holds because the order is total, "a <= b" iff "!(b < a)".
lemma LessEqualIsTheClosure(a: fp64, b: fp64) {
  assert a == b ==> a <= b;
  assert a < b ==> a <= b;
  assert a <= b ==> a < b || a == b;
  assert !(a < a);
  assert a <= a;
}

// The unchecked static methods keep raw IEEE comparison, which leaves the two zeros tied and makes
// every NaN comparison false. This mirrors fp*.Equal keeping IEEE equality while "==" is value
// identity: the static-method family is the IEEE view, the operators are Dafny's.
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

lemma UncheckedMethodsLeaveNaNUnordered(x: fp64)
  requires !x.IsNaN
{
  assert x < fp64.NaN;                     // operator: NaN is the top
  assert !fp64.Less(x, fp64.NaN);          // method: IEEE says false in both directions
  assert !fp64.Less(fp64.NaN, x);
  assert !fp64.LessOrEqual(x, fp64.NaN);
  assert !fp64.LessOrEqual(fp64.NaN, fp64.NaN);
}

// fp*.Min and fp*.Max are IEEE fp.min/fp.max, not the order's minimum and maximum, and they part
// company with the order at both of the places where Dafny departs from IEEE. At NaN, IEEE DISCARDS
// rather than propagates -- fp.max(NaN, x) is x, so the maximum of a NaN and a number is the
// number, where the order says NaN is the larger. At the signed zeros, SMT-LIB leaves the result
// free to be either zero, so nothing about that case is provable. Away from both they coincide,
// which is the region where anything is at stake.
//
// Nothing needs fixing there: a user who wants the order's minimum writes it, and the result is
// better behaved than fp.min -- total, so no precondition, and correct at the zeros and at NaN.
// FpTotalOrderNeedsCaseSplitZero.dfy carries the quantified bound properties.
function OrderMin(x: fp64, y: fp64): fp64 { if x < y then x else y }
function OrderMax(x: fp64, y: fp64): fp64 { if x < y then y else x }

lemma TheOrdersMinAndMaxAreOneLine() {
  assert OrderMin(-0.0, 0.0) == -0.0 && OrderMax(-0.0, 0.0) == 0.0;
  assert OrderMin(1.0, fp64.NaN) == 1.0 && OrderMax(1.0, fp64.NaN) == fp64.NaN;
}

lemma IeeeMinAgreesWithTheOrderAwayFromZero(x: fp64, y: fp64)
  requires !x.IsNaN && !y.IsNaN && !x.IsZero && !y.IsZero
{
  assert fp64.Min(x, y) == OrderMin(x, y);
  assert fp64.Max(x, y) == OrderMax(x, y);
}

// And where they disagree, that is now sayable: fp*.Min and fp*.Max carry no obligations, so a NaN
// argument can be passed and the discarding observed. This was four errors before the fp*. family
// was made uniformly IEEE.
lemma IeeeMinAndMaxDiscardANaN(x: fp64)
  requires !x.IsNaN
{
  assert fp64.Min(fp64.NaN, x) == x;
  assert fp64.Max(fp64.NaN, x) == x;    // IEEE: the number wins
  assert x < fp64.NaN;                  // the order: NaN is the larger
  assert fp64.Max(fp64.NaN, x) != OrderMax(fp64.NaN, x);
  assert fp64.Min(fp64.NaN, fp64.NaN).IsNaN;   // two NaNs leave nothing to discard
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
