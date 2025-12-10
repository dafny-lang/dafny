// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Test wellformedness checks on fp32 operators

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

method ComparisonNaN(x: fp32, y: fp32) {
  var _ := x < y;   // ERROR x2: requires !x.IsNaN && !y.IsNaN
  var _ := x <= y;  // ERROR x2
  var _ := x > y;   // ERROR x2
  var _ := x >= y;  // ERROR x2
}

method MathFunctionsNaN(x: fp32, y: fp32) {
  var _ := fp32.Floor(x);    // ERROR: requires !x.IsNaN
  var _ := fp32.Ceiling(x);  // ERROR
  var _ := fp32.Round(x);    // ERROR
  var _ := fp32.Abs(x);      // ERROR
  var _ := fp32.Sqrt(x);     // ERROR x2: requires !x.IsNaN && !x.IsNegative
  var _ := fp32.Sqrt(-1.0);  // ERROR: requires !x.IsNegative
  var _ := fp32.Min(x, y);   // ERROR x2: requires !x.IsNaN && !y.IsNaN
  var _ := fp32.Max(x, y);   // ERROR x2
  var _ := fp32.ToInt(x);    // ERROR: requires x.IsFinite
  var _ := fp32.ToInt(fp32.PositiveInfinity);  // ERROR
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
