// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Test wellformedness checks on fp64 operators

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

method ComparisonNaN(x: fp64, y: fp64) {
  var _ := x < y;   // ERROR x2: requires !x.IsNaN && !y.IsNaN
  var _ := x <= y;  // ERROR x2
  var _ := x > y;   // ERROR x2
  var _ := x >= y;  // ERROR x2
}

method MathFunctionsNaN(x: fp64, y: fp64) {
  var _ := fp64.Floor(x);    // ERROR: requires !x.IsNaN
  var _ := fp64.Ceiling(x);  // ERROR
  var _ := fp64.Round(x);    // ERROR
  var _ := fp64.Abs(x);      // ERROR
  var _ := fp64.Sqrt(x);     // ERROR x2: requires !x.IsNaN && !x.IsNegative
  var _ := fp64.Sqrt(-1.0);  // ERROR: requires !x.IsNegative
  var _ := fp64.Min(x, y);   // ERROR x2: requires !x.IsNaN && !y.IsNaN
  var _ := fp64.Max(x, y);   // ERROR x2
  var _ := fp64.ToInt(x);    // ERROR: requires x.IsFinite
  var _ := fp64.ToInt(fp64.PositiveInfinity);  // ERROR
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
