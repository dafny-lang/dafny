// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// As Fp64Wellformedness.dfy at the other width: the operators carry obligations, the fp32.* static
// methods are IEEE and carry none, and fp32.ToInt is the single exception.

method ArithmeticNaN(x: fp32, y: fp32) {
  var _ := x + y;  // ERROR x2: requires !x.IsNaN && !y.IsNaN
  var _ := x - y;  // ERROR x2
  var _ := x * y;  // ERROR x2
  var _ := x / y;  // ERROR x3: !x.IsNaN && !y.IsNaN && !y.IsZero
  var _ := -x;     // ERROR: requires !x.IsNaN
}

method InvalidInfinity() {
  var inf := fp32.PositiveInfinity;
  var _ := inf + (-inf);  // ERROR: ∞ + (-∞)
  var _ := inf - inf;     // ERROR: ∞ - ∞
  var _ := inf * 0.0;     // ERROR: ∞ * 0
  var _ := 0.0 / 0.0;     // ERROR: 0 / 0
  var _ := inf / inf;     // ERROR: ∞ / ∞
}

// As Fp64Wellformedness.ComparisonNaN: comparison carries no NaN obligation, because the order is
// total and the result is a bool rather than a float.
method ComparisonNaN(x: fp32, y: fp32) {
  var _ := x < y;   // OK on arbitrary operands
  var _ := x <= y;  // OK
  var _ := x > y;   // OK
  var _ := x >= y;  // OK
}

// As Fp64Wellformedness.TheFamilyIsUniformlyIeee: the fp32.* methods are the IEEE operations and
// carry no obligations, so each is total on arbitrary arguments.
method TheFamilyIsUniformlyIeee(x: fp32, y: fp32) {
  var _ := fp32.Add(x, y);
  var _ := fp32.Div(x, y);
  var _ := fp32.Neg(x);
  var _ := fp32.Sqrt(x);
  var _ := fp32.Sqrt(-1.0);   // IEEE: NaN
  var _ := fp32.Sqrt(-0.0);   // IEEE: -0.0
  var _ := fp32.Floor(x);
  var _ := fp32.Ceiling(x);
  var _ := fp32.Round(x);
  var _ := fp32.Abs(x);
  var _ := fp32.Min(x, y);
  var _ := fp32.Max(x, y);
  var _ := fp32.Less(x, y);
  var _ := fp32.Equal(x, y);
}

// ToInt keeps its obligation: fp.to_sbv of a NaN or infinity is an unspecified integer, not a NaN,
// so no IEEE version can exist. One call per method, since ToInt is expensive to prove about.
method ToIntIsTheOneCheckedMethod(x: fp32) {
  var _ := fp32.ToInt(x);    // ERROR: requires x.IsFinite
}

method ToIntRefusesInfinity() {
  var _ := fp32.ToInt(fp32.PositiveInfinity);  // ERROR
}

method ToIntRefusesNaN() {
  var _ := fp32.ToInt(fp32.NaN);               // ERROR
}

method CorrectUsage(x: fp32, y: fp32)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsInfinite && y.IsInfinite && x.IsPositive != y.IsPositive)
  requires !y.IsZero
{
  var _ := x + y;  // OK
  var _ := x < y;  // OK
}
