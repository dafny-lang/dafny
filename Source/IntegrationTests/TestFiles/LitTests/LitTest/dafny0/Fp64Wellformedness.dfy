// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Which fp64 operations carry well-formedness obligations, and which do not.
//
// The rule is that the OPERATORS are Dafny's, and carry obligations, while the fp64.* static
// methods are the IEEE operations and carry none. fp64.ToInt is the single exception, and its
// reason is different in kind: see ToIntIsTheOneCheckedMethod below.

method ArithmeticNaN(x: fp64, y: fp64) {
  var _ := x + y;  // ERROR x2: requires !x.IsNaN && !y.IsNaN
  var _ := x - y;  // ERROR x2
  var _ := x * y;  // ERROR x2
  var _ := x / y;  // ERROR x3: !x.IsNaN && !y.IsNaN && !y.IsZero
  var _ := -x;     // ERROR: requires !x.IsNaN
}

method InvalidInfinity() {
  var inf := fp64.PositiveInfinity;
  var _ := inf + (-inf);  // ERROR: ∞ + (-∞)
  var _ := inf - inf;     // ERROR: ∞ - ∞
  var _ := inf * 0.0;     // ERROR: ∞ * 0
  var _ := 0.0 / 0.0;     // ERROR: 0 / 0
  var _ := inf / inf;     // ERROR: ∞ / ∞
}

// Comparison carries no NaN obligation, unlike the arithmetic above: its result is a bool, so there
// is no unrequested NaN to prevent, and the order is total. Generating no obligation at all, this
// method adds nothing to the "verified" count; what pins it is the absence of errors here from
// the .expect file.
method ComparisonNaN(x: fp64, y: fp64) {
  var _ := x < y;   // OK on arbitrary operands
  var _ := x <= y;  // OK
  var _ := x > y;   // OK
  var _ := x >= y;  // OK
}

// The whole fp64.* family on unconstrained arguments, with no errors expected. These are the IEEE
// operations, so each is total: where the operation has no numeric result it answers NaN, and there
// is nothing for an obligation to prevent. An obligation on any of them would also buy no safety --
// see NaNFromTheFamilyStillCannotReachArithmetic.
method TheFamilyIsUniformlyIeee(x: fp64, y: fp64) {
  var _ := fp64.Add(x, y);
  var _ := fp64.Sub(x, y);
  var _ := fp64.Mul(x, y);
  var _ := fp64.Div(x, y);
  var _ := fp64.Neg(x);
  var _ := fp64.Sqrt(x);
  var _ := fp64.Sqrt(-1.0);   // IEEE: NaN
  var _ := fp64.Sqrt(-0.0);   // IEEE: -0.0, which fp.isNegative(-0.0) would wrongly exclude
  var _ := fp64.Floor(x);
  var _ := fp64.Ceiling(x);
  var _ := fp64.Round(x);
  var _ := fp64.Abs(x);
  var _ := fp64.Min(x, y);
  var _ := fp64.Max(x, y);
  var _ := fp64.Less(x, y);
  var _ := fp64.LessOrEqual(x, y);
  var _ := fp64.Greater(x, y);
  var _ := fp64.GreaterOrEqual(x, y);
  var _ := fp64.Equal(x, y);
  var _ := fp64.FromReal(0.1);
  var _ := fp32.FromFp64(x);
}

// A NaN reaching arithmetic is stopped there whatever produced it, so the diagnostic sits at the use
// rather than at the method.
method NaNFromTheFamilyStillCannotReachArithmetic(x: fp64) returns (r: fp64) {
  var s := fp64.Sqrt(-1.0);
  r := s + 1.0;              // ERROR: + requires operands that are not NaN
}

// And a NaN that is only compared or printed needs no obligation at all, the order being total.
method NaNFromTheFamilyIsFineOutsideArithmetic() returns (b: bool) {
  var s := fp64.Sqrt(-1.0);
  b := s < 1.0;              // OK
  assert !b;                 // NaN is the maximum, so it is below nothing
  assert s == fp64.NaN;      // and there is exactly one NaN
}

// ToInt is the one checked method: fp.to_sbv of a NaN or an infinity is an UNSPECIFIED integer
// rather than a NaN, so there is no IEEE answer to fall back on.
//
// One call per method, ToInt going through fp.to_real, which is expensive enough that several in one
// proof context exceed the time limit.
method ToIntIsTheOneCheckedMethod(x: fp64) {
  var _ := fp64.ToInt(x);                      // ERROR: requires x.IsFinite
}

method ToIntRefusesInfinity() {
  var _ := fp64.ToInt(fp64.PositiveInfinity);  // ERROR
}

method ToIntRefusesNaN() {
  var _ := fp64.ToInt(fp64.NaN);               // ERROR
}

method CorrectUsage(x: fp64, y: fp64)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsInfinite && y.IsInfinite && x.IsPositive != y.IsPositive)
  requires !y.IsZero
{
  var _ := x + y;  // OK
  var _ := x < y;  // OK
}
