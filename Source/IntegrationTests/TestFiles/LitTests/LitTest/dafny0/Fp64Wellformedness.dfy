// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Comprehensive fp64 well-formedness tests
// Tests ALL preconditions from design doc section 7.3 (except equality which is tested separately)

// ===== ARITHMETIC: NaN CHECKS =====

method TestAdditionNaN(x: fp64, y: fp64) returns (r: fp64) {
  r := x + y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestSubtractionNaN(x: fp64, y: fp64) returns (r: fp64) {
  r := x - y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestMultiplicationNaN(x: fp64, y: fp64) returns (r: fp64) {
  r := x * y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestDivisionNaN(x: fp64, y: fp64) returns (r: fp64) {
  r := x / y;  // ERROR: needs !x.IsNaN && !y.IsNaN && !y.IsZero
}

method TestNegationNaN(x: fp64) returns (r: fp64) {
  r := -x;  // ERROR: needs !x.IsNaN
}

// ===== ARITHMETIC: INFINITY CHECKS =====

method TestAdditionInfinity() returns (r: fp64) {
  var posInf := fp64.PositiveInfinity;
  var negInf := fp64.NegativeInfinity;
  r := posInf + negInf;  // ERROR: ∞ + (-∞) is invalid
}

method TestSubtractionInfinity() returns (r: fp64) {
  var posInf := fp64.PositiveInfinity;
  r := posInf - posInf;  // ERROR: ∞ - ∞ is invalid
}

method TestMultiplicationInfZero() returns (r: fp64) {
  var inf := fp64.PositiveInfinity;
  r := inf * 0.0;  // ERROR: ∞ * 0 is invalid
}

method TestDivisionZeroZero() returns (r: fp64) {
  r := 0.0 / 0.0;  // ERROR: 0 / 0 is invalid
}

method TestDivisionInfInf() returns (r: fp64) {
  var inf := fp64.PositiveInfinity;
  r := inf / inf;  // ERROR: ∞ / ∞ is invalid
}

// ===== COMPARISON OPERATIONS =====

method TestLessThanNaN(x: fp64, y: fp64) returns (r: bool) {
  r := x < y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestLessEqualNaN(x: fp64, y: fp64) returns (r: bool) {
  r := x <= y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestGreaterThanNaN(x: fp64, y: fp64) returns (r: bool) {
  r := x > y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestGreaterEqualNaN(x: fp64, y: fp64) returns (r: bool) {
  r := x >= y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

// ===== MATHEMATICAL FUNCTIONS =====

method TestFloorNaN(x: fp64) returns (r: fp64) {
  r := fp64.Floor(x);  // ERROR: needs !x.IsNaN
}

method TestCeilingNaN(x: fp64) returns (r: fp64) {
  r := fp64.Ceiling(x);  // ERROR: needs !x.IsNaN
}

method TestRoundNaN(x: fp64) returns (r: fp64) {
  r := fp64.Round(x);  // ERROR: needs !x.IsNaN
}

method TestAbsNaN(x: fp64) returns (r: fp64) {
  r := fp64.Abs(x);  // ERROR: needs !x.IsNaN
}

method TestSqrtNaN(x: fp64) returns (r: fp64) {
  r := fp64.Sqrt(x);  // ERROR: needs !x.IsNaN && !x.IsNegative
}

method TestSqrtNegative() returns (r: fp64) {
  r := fp64.Sqrt(-1.0);  // ERROR: needs !x.IsNegative
}

method TestMinNaN(x: fp64, y: fp64) returns (r: fp64) {
  r := fp64.Min(x, y);  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestMaxNaN(x: fp64, y: fp64) returns (r: fp64) {
  r := fp64.Max(x, y);  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestToIntNonFinite(x: fp64) returns (r: int) {
  r := fp64.ToInt(x);  // ERROR: needs x.IsFinite
}

method TestToIntInfinity() returns (r: int) {
  var inf := fp64.PositiveInfinity;
  r := fp64.ToInt(inf);  // ERROR: infinity is not finite
}

method TestToIntNaN() returns (r: int) {
  var nan := fp64.NaN;
  r := fp64.ToInt(nan);  // ERROR: NaN is not finite
}

// ===== CORRECT USAGE WITH FULL PRECONDITIONS =====

method TestAdditionCorrect(x: fp64, y: fp64) returns (r: fp64)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsInfinite && y.IsInfinite && x.IsPositive != y.IsPositive)
{
  r := x + y;  // OK
}

method TestDivisionCorrect(x: fp64, y: fp64) returns (r: fp64)
  requires !x.IsNaN && !y.IsNaN
  requires !y.IsZero
  requires !(x.IsZero && y.IsZero)
  requires !(x.IsInfinite && y.IsInfinite)
{
  r := x / y;  // OK
}

method TestSqrtCorrect(x: fp64) returns (r: fp64)
  requires !x.IsNaN && !x.IsNegative
{
  r := fp64.Sqrt(x);  // OK
}

method TestComparisonCorrect(x: fp64, y: fp64) returns (r: bool)
  requires !x.IsNaN && !y.IsNaN
{
  r := x < y;  // OK
}

method TestFloorCorrect(x: fp64) returns (r: fp64)
  requires !x.IsNaN
{
  r := fp64.Floor(x);  // OK
}
