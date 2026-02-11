// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

// Test for fp64 additional special values
// Tests special constants like PositiveZero, NegativeZero, MaxValue, MinValue, etc.

method TestZeroValues() {
  // Test positive and negative zero literals
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // Verify zeros have different bit patterns (Dafny == is bitwise)
  assert pos_zero != neg_zero;  // Different bit patterns

  // Test classification
  assert pos_zero.IsZero;
  assert neg_zero.IsZero;
  assert !pos_zero.IsNegative;
  assert neg_zero.IsNegative;
  assert pos_zero.IsPositive;
  assert !neg_zero.IsPositive;

  // Test arithmetic preserving zero sign
  var sum_pos := pos_zero + pos_zero;
  var sum_neg := neg_zero + neg_zero;
  assert sum_pos.IsZero && !sum_pos.IsNegative;
  assert sum_neg.IsZero && sum_neg.IsNegative;

  // Test negation of zero variables (not just literals)
  var neg_of_pos_zero := -pos_zero;  // Should produce -0.0
  var neg_of_neg_zero := -neg_zero;  // Should produce +0.0
  assert neg_of_pos_zero.IsZero;
  assert neg_of_pos_zero.IsNegative;
  assert neg_of_neg_zero.IsZero;
  assert !neg_of_neg_zero.IsNegative;  // Double negation should give positive zero

  // Verify they have the correct bit patterns
  assert neg_of_pos_zero == neg_zero;  // -pos_zero should equal -0.0
  assert neg_of_neg_zero == pos_zero;  // -neg_zero should equal +0.0
}

method TestBoundaryValues() {
  // Test maximum and minimum finite values
  var max_val := fp64.MaxValue;
  var min_val := fp64.MinValue;  // Most negative finite value

  // Test properties
  assert max_val.IsFinite;
  assert max_val.IsNormal;
  assert max_val.IsPositive;
  assert !max_val.IsInfinite;

  assert min_val.IsFinite;
  assert min_val.IsNormal;
  assert min_val.IsNegative;
  assert !min_val.IsInfinite;

  // Test that max and min have opposite signs but same magnitude
  assert fp64.Abs(min_val) == max_val;

  // Test overflow behavior
  var overflow_test := max_val * 2.0;
  assert overflow_test.IsInfinite && overflow_test.IsPositive;
  assert overflow_test == fp64.PositiveInfinity;  // Verify overflow creates the constant

  var negative_overflow_test := min_val * 2.0;
  assert negative_overflow_test.IsInfinite && negative_overflow_test.IsNegative;
  assert negative_overflow_test == fp64.NegativeInfinity;  // Verify overflow creates the constant

  // Test that operations on max value can produce finite results
  var safe_op := max_val / 2.0;
  assert safe_op.IsFinite;
}

method TestSmallestValues() {
  // Test smallest positive values
  var min_normal := fp64.MinNormal;     // Smallest normal positive value
  var min_subnormal := fp64.MinSubnormal; // Smallest subnormal positive value (aka MinPositive)

  // Test properties of smallest normal
  assert min_normal.IsFinite;
  assert min_normal.IsNormal;
  assert !min_normal.IsSubnormal;
  assert min_normal.IsPositive;

  // Test properties of smallest subnormal
  assert min_subnormal.IsFinite;
  assert !min_subnormal.IsNormal;
  assert min_subnormal.IsSubnormal;
  assert min_subnormal.IsPositive;
  assert min_subnormal < min_normal;

  // Test that smallest subnormal is truly the smallest positive
  var half_min := min_subnormal / 2.0;
  assert half_min.IsZero;  // Underflows to zero
  assert half_min.IsPositive;  // Should underflow to positive zero

  // Test underflow to negative zero
  var neg_half_min := (-min_subnormal) / 2.0;
  assert neg_half_min.IsZero;
  assert neg_half_min.IsNegative;  // Should underflow to negative zero
}

method TestEpsilonValue() {
  // Test machine epsilon - smallest value such that 1.0 + epsilon != 1.0
  var epsilon := fp64.Epsilon;

  // Test epsilon property
  var one: fp64 := 1.0;
  var one_plus_eps := one + epsilon;
  var one_plus_half_eps := one + (epsilon / 2.0);

  assert one_plus_eps != one;
  assert one_plus_half_eps == one;  // Too small to make a difference

  // Epsilon should be 2^-52 for fp64
  assert epsilon.IsFinite;
  assert epsilon.IsNormal;
  assert epsilon.IsPositive;
}

method TestSpecialValueComparisons() {
  // Test comparisons with special values
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;
  var max_val := fp64.MaxValue;
  var normal: fp64 := 42.0;
  var pos_zero := 0.0;
  var neg_zero := -0.0;

  // Infinity comparisons
  assert neg_inf < normal;
  assert normal < pos_inf;
  assert neg_inf < pos_inf;
  assert pos_inf > max_val;
  assert neg_inf < fp64.MinValue;

  // Special value ordering
  assert neg_inf < fp64.MinValue;
  assert fp64.MinValue < neg_zero;
  assert neg_zero <= pos_zero;
  assert pos_zero < fp64.MinSubnormal;
  assert fp64.MinSubnormal < fp64.MinNormal;
  assert fp64.MinNormal < 1.0;
  assert 1.0 < fp64.MaxValue;
  assert fp64.MaxValue < pos_inf;
}

method TestSpecialValueProperties() {
  // Test that special values have expected properties

  // PositiveInfinity properties
  var pos_inf := fp64.PositiveInfinity;
  assert pos_inf.IsInfinite;
  assert !pos_inf.IsFinite;
  assert !pos_inf.IsNaN;
  assert pos_inf.IsPositive;
  assert !pos_inf.IsNegative;
  assert !pos_inf.IsZero;
  assert !pos_inf.IsNormal;
  assert !pos_inf.IsSubnormal;

  // NegativeInfinity properties
  var neg_inf := fp64.NegativeInfinity;
  assert neg_inf.IsInfinite;
  assert !neg_inf.IsFinite;
  assert !neg_inf.IsNaN;
  assert !neg_inf.IsPositive;
  assert neg_inf.IsNegative;
  assert !neg_inf.IsZero;
  assert !neg_inf.IsNormal;
  assert !neg_inf.IsSubnormal;
}

method TestUsefulDerivedConstants() {
  // Common mathematical constants
  var pi := fp64.Pi;
  var e := fp64.E;

  // Verify some properties
  assert ~3.14 < pi < ~3.15;
  assert ~2.71 < e < ~2.72;
}

method TestHardcodedLiterals() {
  // Test that specific hardcoded literal approximations round to expected fp64 values

  // Smallest positive normal number
  var min_normal_literal: fp64 := ~2.2250738585072014e-308;  // Should round to 2^(-1022)
  assert min_normal_literal == fp64.MinNormal;

  // Smallest positive subnormal number
  var min_subnormal_literal: fp64 := ~4.9406564584124654e-324;  // Should round to 2^(-1074)
  assert min_subnormal_literal == fp64.MinSubnormal;

  // Largest finite number
  var max_value_literal: fp64 := ~1.7976931348623157e308;  // Should round to (2-2^(-52))*2^1023
  assert max_value_literal == fp64.MaxValue;

  // Machine epsilon (difference between 1.0 and next representable number)
  var epsilon_literal: fp64 := ~2.220446049250313e-16;  // Should round to 2^(-52)
  assert epsilon_literal == fp64.Epsilon;

  // Values close to 1.0
  var next_up_1: fp64 := ~1.0000000000000002;  // Should round to 1 + 2^(-52)
  var next_down_1: fp64 := ~0.9999999999999999;  // Should round to 1 - 2^(-53)

  // Verify next_up_1 is the next representable value after 1.0
  assert next_up_1 > 1.0;
  assert next_up_1 == 1.0 + fp64.Epsilon;

  // Verify next_down_1 is the previous representable value before 1.0
  assert next_down_1 < 1.0;
}

method TestNaNBehavior() {
  // Test NaN behavior
  var nan: fp64 := fp64.NaN;
  var x: fp64 := 1.0;

  // NaN propagation in arithmetic - all produce NaN
  var nan_plus_x := fp64.Add(nan, x);
  assert nan_plus_x.IsNaN;  // NaN + anything = NaN

  var nan_minus_x := fp64.Sub(nan, x);
  assert nan_minus_x.IsNaN;  // NaN - anything = NaN

  var nan_times_x := fp64.Mul(nan, x);
  assert nan_times_x.IsNaN;  // NaN * anything = NaN

  var nan_div_x := fp64.Div(nan, x);
  assert nan_div_x.IsNaN;  // NaN / anything = NaN

  var x_div_nan := fp64.Div(x, nan);
  assert x_div_nan.IsNaN;  // anything / NaN = NaN

  // NaN comparisons - all return false per IEEE 754
  var nan_less_x := fp64.Less(nan, x);
  assert !nan_less_x;  // NaN < anything = false

  var nan_greater_x := fp64.Greater(nan, x);
  assert !nan_greater_x;  // NaN > anything = false

  var nan_less_eq_x := fp64.LessOrEqual(nan, x);
  assert !nan_less_eq_x;  // NaN <= anything = false

  var nan_greater_eq_x := fp64.GreaterOrEqual(nan, x);
  assert !nan_greater_eq_x;  // NaN >= anything = false

  // NaN equality per IEEE 754
  var nan_equal_nan := fp64.Equal(nan, nan);
  assert !nan_equal_nan;  // NaN != NaN per IEEE 754

  var nan_equal_x := fp64.Equal(nan, x);
  assert !nan_equal_x;  // NaN != anything

  // Also test comparisons with NaN on the right
  assert !fp64.Less(x, nan);           // anything < NaN = false
  assert !fp64.Greater(x, nan);        // anything > NaN = false
  assert !fp64.LessOrEqual(x, nan);    // anything <= NaN = false
  assert !fp64.GreaterOrEqual(x, nan); // anything >= NaN = false
}

method TestInfinityBehavior() {
  // Test infinity behavior
  var pos_inf: fp64 := fp64.PositiveInfinity;
  var neg_inf: fp64 := fp64.NegativeInfinity;
  var x: fp64 := 1.0;

  // Arithmetic with positive infinity
  var pos_inf_plus_x := pos_inf + x;
  assert pos_inf_plus_x.IsInfinite && pos_inf_plus_x.IsPositive;  // +∞ + finite = +∞

  var pos_inf_minus_x := pos_inf - x;
  assert pos_inf_minus_x.IsInfinite && pos_inf_minus_x.IsPositive;  // +∞ - finite = +∞

  var pos_inf_times_x := pos_inf * x;
  assert pos_inf_times_x.IsInfinite && pos_inf_times_x.IsPositive;  // +∞ * positive = +∞

  var pos_inf_times_neg_x := pos_inf * -x;
  assert pos_inf_times_neg_x.IsInfinite && pos_inf_times_neg_x.IsNegative;  // +∞ * negative = -∞

  var pos_inf_div_x := pos_inf / x;
  assert pos_inf_div_x.IsInfinite && pos_inf_div_x.IsPositive;  // +∞ / positive = +∞

  var x_div_pos_inf := x / pos_inf;
  assert x_div_pos_inf.IsZero && !x_div_pos_inf.IsNegative;  // finite / +∞ = +0

  // Arithmetic with negative infinity
  var neg_inf_plus_x := neg_inf + x;
  assert neg_inf_plus_x.IsInfinite && neg_inf_plus_x.IsNegative;  // -∞ + finite = -∞

  var neg_inf_minus_x := neg_inf - x;
  assert neg_inf_minus_x.IsInfinite && neg_inf_minus_x.IsNegative;  // -∞ - finite = -∞

  var neg_inf_times_x := neg_inf * x;
  assert neg_inf_times_x.IsInfinite && neg_inf_times_x.IsNegative;  // -∞ * positive = -∞

  var neg_inf_times_neg_x := neg_inf * -x;
  assert neg_inf_times_neg_x.IsInfinite && neg_inf_times_neg_x.IsPositive;  // -∞ * negative = +∞

  var neg_inf_div_x := neg_inf / x;
  assert neg_inf_div_x.IsInfinite && neg_inf_div_x.IsNegative;  // -∞ / positive = -∞

  var x_div_neg_inf := x / neg_inf;
  assert x_div_neg_inf.IsZero && x_div_neg_inf.IsNegative;  // positive / -∞ = -0

  // Special cases that produce NaN
  var pos_inf_minus_pos_inf := fp64.Sub(pos_inf, pos_inf);
  assert pos_inf_minus_pos_inf.IsNaN;  // ∞ - ∞ = NaN

  var pos_inf_div_pos_inf := fp64.Div(pos_inf, pos_inf);
  assert pos_inf_div_pos_inf.IsNaN;  // ∞ / ∞ = NaN

  var zero_times_pos_inf := fp64.Mul(0.0, pos_inf);
  assert zero_times_pos_inf.IsNaN;  // 0 * ∞ = NaN

  var neg_inf_plus_inf := fp64.Add(neg_inf, pos_inf);
  assert neg_inf_plus_inf.IsNaN;  // -∞ + ∞ = NaN

  var zero_times_neg_inf := fp64.Mul(0.0, neg_inf);
  assert zero_times_neg_inf.IsNaN;  // 0 * -∞ = NaN

  // Special cases that produce infinity
  var pos_inf_times_pos_inf := pos_inf * pos_inf;
  assert pos_inf_times_pos_inf.IsInfinite && pos_inf_times_pos_inf.IsPositive;  // +∞ * +∞ = +∞

  var pos_inf_times_neg_inf := pos_inf * neg_inf;
  assert pos_inf_times_neg_inf.IsInfinite && pos_inf_times_neg_inf.IsNegative;  // +∞ * -∞ = -∞

  var neg_inf_times_neg_inf := neg_inf * neg_inf;
  assert neg_inf_times_neg_inf.IsInfinite && neg_inf_times_neg_inf.IsPositive;  // -∞ * -∞ = +∞

  // Comparisons with infinity
  assert pos_inf > x;       // +∞ > any finite
  assert neg_inf < x;       // -∞ < any finite
  assert pos_inf > neg_inf;  // +∞ > -∞
}

method TestStaticArithmeticMethods() {
  // Test that static arithmetic methods work correctly for normal cases
  var x: fp64 := 5.0;
  var y: fp64 := 3.0;

  // Normal arithmetic
  assert fp64.Add(1.0, 2.0) == 3.0;
  assert fp64.Sub(5.0, 3.0) == 2.0;
  assert fp64.Mul(2.0, 3.0) == 6.0;
  assert fp64.Div(6.0, 2.0) == 3.0;
  assert fp64.Neg(5.0) == -5.0;

  // Equivalence with operators (when preconditions hold)
  assert fp64.Add(x, y) == x + y;
  assert fp64.Sub(x, y) == x - y;
  assert fp64.Mul(x, y) == x * y;
  assert fp64.Div(x, y) == x / y;

  // Negation edge cases
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;

  assert fp64.Neg(nan).IsNaN;
  assert fp64.Neg(inf) == neg_inf;
  assert fp64.Neg(neg_inf) == inf;
  assert fp64.Neg(0.0) == -0.0;
  assert fp64.Neg(-0.0) == 0.0;
}

method Main() {
  TestZeroValues();
  TestBoundaryValues();
  TestSmallestValues();
  TestEpsilonValue();
  TestSpecialValueComparisons();
  TestSpecialValueProperties();
  TestUsefulDerivedConstants();
  TestHardcodedLiterals();
  TestNaNBehavior();
  TestInfinityBehavior();
  TestStaticArithmeticMethods();
}