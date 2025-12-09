// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Comprehensive fp32 well-formedness tests
// Tests ALL preconditions from design doc section 7.3 (except equality which is tested separately)

// ===== ARITHMETIC: NaN CHECKS =====

method TestAdditionNaN(x: fp32, y: fp32) returns (r: fp32) {
  r := x + y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestSubtractionNaN(x: fp32, y: fp32) returns (r: fp32) {
  r := x - y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestMultiplicationNaN(x: fp32, y: fp32) returns (r: fp32) {
  r := x * y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestDivisionNaN(x: fp32, y: fp32) returns (r: fp32) {
  r := x / y;  // ERROR: needs !x.IsNaN && !y.IsNaN && !y.IsZero
}

method TestNegationNaN(x: fp32) returns (r: fp32) {
  r := -x;  // ERROR: needs !x.IsNaN
}

// ===== ARITHMETIC: INFINITY CHECKS =====

method TestAdditionInfinity() returns (r: fp32) {
  var posInf := fp32.PositiveInfinity;
  var negInf := fp32.NegativeInfinity;
  r := posInf + negInf;  // ERROR: ∞ + (-∞) is invalid
}

method TestSubtractionInfinity() returns (r: fp32) {
  var posInf := fp32.PositiveInfinity;
  r := posInf - posInf;  // ERROR: ∞ - ∞ is invalid
}

method TestMultiplicationInfZero() returns (r: fp32) {
  var inf := fp32.PositiveInfinity;
  r := inf * 0.0;  // ERROR: ∞ * 0 is invalid
}

method TestDivisionZeroZero() returns (r: fp32) {
  r := 0.0 / 0.0;  // ERROR: 0 / 0 is invalid
}

method TestDivisionInfInf() returns (r: fp32) {
  var inf := fp32.PositiveInfinity;
  r := inf / inf;  // ERROR: ∞ / ∞ is invalid
}

// ===== COMPARISON OPERATIONS =====

method TestLessThanNaN(x: fp32, y: fp32) returns (r: bool) {
  r := x < y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestLessEqualNaN(x: fp32, y: fp32) returns (r: bool) {
  r := x <= y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestGreaterThanNaN(x: fp32, y: fp32) returns (r: bool) {
  r := x > y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestGreaterEqualNaN(x: fp32, y: fp32) returns (r: bool) {
  r := x >= y;  // ERROR: needs !x.IsNaN && !y.IsNaN
}

// ===== MATHEMATICAL FUNCTIONS =====

method TestFloorNaN(x: fp32) returns (r: fp32) {
  r := fp32.Floor(x);  // ERROR: needs !x.IsNaN
}

method TestCeilingNaN(x: fp32) returns (r: fp32) {
  r := fp32.Ceiling(x);  // ERROR: needs !x.IsNaN
}

method TestRoundNaN(x: fp32) returns (r: fp32) {
  r := fp32.Round(x);  // ERROR: needs !x.IsNaN
}

method TestAbsNaN(x: fp32) returns (r: fp32) {
  r := fp32.Abs(x);  // ERROR: needs !x.IsNaN
}

method TestSqrtNaN(x: fp32) returns (r: fp32) {
  r := fp32.Sqrt(x);  // ERROR: needs !x.IsNaN && !x.IsNegative
}

method TestSqrtNegative() returns (r: fp32) {
  r := fp32.Sqrt(-1.0);  // ERROR: needs !x.IsNegative
}

method TestMinNaN(x: fp32, y: fp32) returns (r: fp32) {
  r := fp32.Min(x, y);  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestMaxNaN(x: fp32, y: fp32) returns (r: fp32) {
  r := fp32.Max(x, y);  // ERROR: needs !x.IsNaN && !y.IsNaN
}

method TestToIntNonFinite(x: fp32) returns (r: int) {
  r := fp32.ToInt(x);  // ERROR: needs x.IsFinite
}

method TestToIntInfinity() returns (r: int) {
  var inf := fp32.PositiveInfinity;
  r := fp32.ToInt(inf);  // ERROR: infinity is not finite
}

method TestToIntNaN() returns (r: int) {
  var nan := fp32.NaN;
  r := fp32.ToInt(nan);  // ERROR: NaN is not finite
}

// ===== CORRECT USAGE WITH FULL PRECONDITIONS =====

method TestAdditionCorrect(x: fp32, y: fp32) returns (r: fp32)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsInfinite && y.IsInfinite && x.IsPositive != y.IsPositive)
{
  r := x + y;  // OK
}

method TestDivisionCorrect(x: fp32, y: fp32) returns (r: fp32)
  requires !x.IsNaN && !y.IsNaN
  requires !y.IsZero
  requires !(x.IsZero && y.IsZero)
  requires !(x.IsInfinite && y.IsInfinite)
{
  r := x / y;  // OK
}

method TestSqrtCorrect(x: fp32) returns (r: fp32)
  requires !x.IsNaN && !x.IsNegative
{
  r := fp32.Sqrt(x);  // OK
}

method TestComparisonCorrect(x: fp32, y: fp32) returns (r: bool)
  requires !x.IsNaN && !y.IsNaN
{
  r := x < y;  // OK
}

method TestFloorCorrect(x: fp32) returns (r: fp32)
  requires !x.IsNaN
{
  r := fp32.Floor(x);  // OK
}
