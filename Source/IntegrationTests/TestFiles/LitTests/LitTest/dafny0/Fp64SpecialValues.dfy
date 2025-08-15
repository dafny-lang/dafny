// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

// Test for fp64 additional special values
// Tests special constants like PositiveZero, NegativeZero, MaxValue, MinValue, etc.

method TestZeroValues() {
  // Test positive and negative zero constants
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // Test literal zeros
  var lit_pos_zero: fp64 := 0.0;
  var lit_neg_zero: fp64 := -0.0;

  // Verify zeros have different bit patterns (Dafny == is bitwise)
  assert pos_zero != neg_zero;  // Different bit patterns
  assert lit_pos_zero != lit_neg_zero;
  assert pos_zero == lit_pos_zero;
  assert neg_zero == lit_neg_zero;

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
  // This catches the bug where -expr is transformed to 0 - expr
  var neg_of_pos_zero := -pos_zero;  // Should produce -0.0
  var neg_of_neg_zero := -neg_zero;  // Should produce +0.0
  assert neg_of_pos_zero.IsZero;
  assert neg_of_pos_zero.IsNegative;  // BUG: This currently fails! -pos_zero produces +0.0
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
  assert overflow_test.IsInfinite;

  var underflow_test := min_val * 2.0;
  assert underflow_test.IsInfinite && underflow_test.IsNegative;
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
  assert min_normal > 0.0;

  // Test properties of smallest subnormal
  assert min_subnormal.IsFinite;
  assert !min_subnormal.IsNormal;
  assert min_subnormal.IsSubnormal;
  assert min_subnormal.IsPositive;
  assert min_subnormal > 0.0;
  assert min_subnormal < min_normal;

  // Test that smallest subnormal is truly the smallest positive
  var half_min := min_subnormal / 2.0;
  assert half_min.IsZero;  // Underflows to zero
  assert !half_min.IsNegative;  // Should underflow to positive zero

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

method TestSpecialValueArithmetic() {
  // Test arithmetic with special values
  var nan := fp64.NaN;
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;
  var max_val := fp64.MaxValue;
  var min_val := fp64.MinValue;
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // NaN arithmetic
  var nan_sum := nan + 1.0;
  var nan_prod := nan * 2.0;
  assert nan_sum.IsNaN;
  assert nan_prod.IsNaN;

  // Infinity arithmetic
  var inf_sum := pos_inf + 1.0;
  var inf_diff := neg_inf - 1.0;
  assert inf_sum.IsInfinite && inf_sum.IsPositive;
  assert inf_diff.IsInfinite && inf_diff.IsNegative;

  // Special cases producing NaN
  var inf_minus_inf := pos_inf - pos_inf;
  var zero_times_inf := pos_zero * pos_inf;
  var inf_div_inf := pos_inf / pos_inf;
  assert inf_minus_inf.IsNaN;
  assert zero_times_inf.IsNaN;
  assert inf_div_inf.IsNaN;

  // Max value operations
  var near_overflow := max_val + max_val;
  assert near_overflow.IsInfinite;

  var safe_op := max_val / 2.0;
  assert safe_op.IsFinite;
}

method TestSpecialValueComparisons() {
  // Test comparisons with special values
  var nan := fp64.NaN;
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;
  var max_val := fp64.MaxValue;
  var normal: fp64 := 42.0;
  var pos_zero := 0.0;
  var neg_zero := -0.0;

  // NaN comparisons (all false except inequality)
  assert !(nan < normal);
  assert !(nan <= normal);
  assert !(nan > normal);
  assert !(nan >= normal);
  assert nan == nan;               // NaN Dafny-equal to itself
  assert !(fp64.Equal(nan,nan));  // NaN not IEEE 754 equal to itself

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

method TestQuietAndSignalingNaN() {
  // Test different NaN values (if supported)
  var qnan := fp64.NaN;  // Quiet NaN (default)

  // In IEEE 754, there are quiet and signaling NaNs
  // Dafny might only support quiet NaN
  assert qnan.IsNaN;
  assert !qnan.IsFinite;
  assert !qnan.IsInfinite;

  // NaN propagation
  var result1 := qnan + 1.0;
  var result2 := fp64.Sqrt(qnan);
  var result3 := fp64.Abs(qnan);
  assert result1.IsNaN;
  assert result2.IsNaN;
  assert result3.IsNaN;
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

  // MaxValue properties
  var max_val := fp64.MaxValue;
  assert !max_val.IsInfinite;
  assert max_val.IsFinite;
  assert !max_val.IsNaN;
  assert max_val.IsPositive;
  assert !max_val.IsNegative;
  assert !max_val.IsZero;
  assert max_val.IsNormal;
  assert !max_val.IsSubnormal;
}

method TestUsefulDerivedConstants() {
  // Test other useful constants that might be provided

  // Common mathematical constants (might be provided as static members)
  var pi := fp64.Pi;
  var e := fp64.E;

  // Verify some properties
  assert pi > ~3.14 && pi < ~3.15;
  assert e > ~2.71 && e < ~2.72;
}

method TestSpecialValueCreation() {
  // Test creating special values through operations

  // Create positive infinity through overflow
  var large: fp64 := fp64.MaxValue;
  var pos_inf_created := large * large;
  assert pos_inf_created.IsInfinite && pos_inf_created.IsPositive;
  assert pos_inf_created == fp64.PositiveInfinity;

  // Create negative infinity
  var neg_inf_created := -large * large;
  assert neg_inf_created.IsInfinite && neg_inf_created.IsNegative;
  assert neg_inf_created == fp64.NegativeInfinity;

  // Create NaN through invalid operations
  var zero: fp64 := 0.0;
  // These operations create NaN following IEEE 754 semantics
  // Some operations create NaN, but Sqrt now has a precondition to prevent it
  // Note: NaN values cannot be compared for equality in compiled contexts
  var nan_created1 := fp64.PositiveInfinity - fp64.PositiveInfinity;
  // var nan_created2 := fp64.Sqrt(-1.0);  // ERROR: precondition prevents negative input
  var nan_propagated := fp64.Sqrt(fp64.NaN);  // OK: NaN propagation is allowed
  assert nan_created1.IsNaN;
  assert nan_propagated.IsNaN;

  // Create negative zero
  var neg_zero_created: fp64 := -0.0;  // Explicit type needed for .IsZero/.IsNegative
  assert neg_zero_created.IsZero;
  assert neg_zero_created.IsNegative;
}

method TestEdgeCasesWithAssertions() {
  // Special values
  var nan: fp64 := fp64.NaN;
  var pos_inf: fp64 := fp64.PositiveInfinity;
  var neg_inf: fp64 := fp64.NegativeInfinity;
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // Smallest positive normal number
  var min_normal: fp64 := ~2.2250738585072014e-308;  // Rounds to 2^(-1022)

  // Smallest positive subnormal number
  var min_subnormal: fp64 := ~4.9406564584124654e-324;  // Rounds to 2^(-1074)

  // Largest finite number
  var max_value: fp64 := ~1.7976931348623157e308;  // Rounds to (2-2^(-52))*2^1023

  // Values close to 1.0
  var next_up_1: fp64 := ~1.0000000000000002;  // Rounds to 1 + 2^(-52)
  var next_down_1: fp64 := ~0.9999999999999999;  // Rounds to 1 - 2^(-53)

  // Machine epsilon (difference between 1.0 and next representable number)
  var epsilon: fp64 := ~2.220446049250313e-16;  // Rounds to 2^(-52)

  // Test classification predicates on edge cases
  assert !nan.IsFinite;
  assert nan.IsNaN;

  assert !pos_inf.IsFinite;
  assert pos_inf.IsInfinite;
  assert pos_inf.IsPositive;

  assert !neg_inf.IsFinite;
  assert neg_inf.IsInfinite;
  assert neg_inf.IsNegative;

  assert pos_zero.IsZero;
  assert pos_zero.IsFinite;
  assert !pos_zero.IsNegative;

  assert neg_zero.IsZero;
  assert neg_zero.IsFinite;
  assert neg_zero.IsNegative;

  assert min_normal.IsNormal;
  assert min_normal.IsFinite;
  assert min_normal.IsPositive;

  assert min_subnormal.IsSubnormal;
  assert min_subnormal.IsFinite;
  assert min_subnormal.IsPositive;

  assert max_value.IsNormal;
  assert max_value.IsFinite;
  assert max_value.IsPositive;
}

method TestNaNBehavior() {
  // Test NaN behavior
  var nan: fp64 := fp64.NaN;
  var x: fp64 := 1.0;

  // NaN propagation in arithmetic - all produce NaN
  var nan_plus_x := nan + x;
  assert nan_plus_x.IsNaN;  // NaN + anything = NaN

  var nan_minus_x := nan - x;
  assert nan_minus_x.IsNaN;  // NaN - anything = NaN

  var nan_times_x := nan * x;
  assert nan_times_x.IsNaN;  // NaN * anything = NaN

  var nan_div_x := nan / x;
  assert nan_div_x.IsNaN;  // NaN / anything = NaN

  var x_div_nan := x / nan;
  assert x_div_nan.IsNaN;  // anything / NaN = NaN

  // NaN comparisons - all return false
  var nan_less_x := nan < x;
  assert !nan_less_x;  // NaN < anything = false

  var nan_greater_x := nan > x;
  assert !nan_greater_x;  // NaN > anything = false

  var nan_less_eq_x := nan <= x;
  assert !nan_less_eq_x;  // NaN <= anything = false

  var nan_greater_eq_x := nan >= x;
  assert !nan_greater_eq_x;  // NaN >= anything = false

  // NaN equality per IEEE 754
  var nan_equal_nan := fp64.Equal(nan, nan);
  assert !nan_equal_nan;  // NaN != NaN per IEEE 754

  var nan_equal_x := fp64.Equal(nan, x);
  assert !nan_equal_x;  // NaN != anything

  // Also test comparisons with NaN on the right
  assert !(x < nan);   // anything < NaN = false
  assert !(x > nan);   // anything > NaN = false
  assert !(x <= nan);  // anything <= NaN = false
  assert !(x >= nan);  // anything >= NaN = false
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
  var pos_inf_minus_pos_inf := pos_inf - pos_inf;
  assert pos_inf_minus_pos_inf.IsNaN;  // ∞ - ∞ = NaN

  var pos_inf_div_pos_inf := pos_inf / pos_inf;
  assert pos_inf_div_pos_inf.IsNaN;  // ∞ / ∞ = NaN

  var zero_times_pos_inf := 0.0 * pos_inf;
  assert zero_times_pos_inf.IsNaN;  // 0 * ∞ = NaN

  var neg_inf_plus_inf := neg_inf + pos_inf;
  assert neg_inf_plus_inf.IsNaN;  // -∞ + ∞ = NaN

  var zero_times_neg_inf := 0.0 * neg_inf;
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

method TestStaticConstantConsistency() {
  // Verify that multiple accesses to static constants return consistent values
  var nan1 := fp64.NaN;
  var nan2 := fp64.NaN;
  // Can't use Equal or == for NaN, but both should be NaN
  assert nan1.IsNaN;
  assert nan2.IsNaN;

  var pos_inf1 := fp64.PositiveInfinity;
  var pos_inf2 := fp64.PositiveInfinity;
  assert fp64.Equal(pos_inf1, pos_inf2);
  assert pos_inf1 == pos_inf2;  // Infinities can use bitwise equality

  var neg_inf1 := fp64.NegativeInfinity;
  var neg_inf2 := fp64.NegativeInfinity;
  assert fp64.Equal(neg_inf1, neg_inf2);
  assert neg_inf1 == neg_inf2;

  // Test other constants for consistency
  var max1 := fp64.MaxValue;
  var max2 := fp64.MaxValue;
  assert max1 == max2;

  var pi1 := fp64.Pi;
  var pi2 := fp64.Pi;
  assert pi1 == pi2;
}

method Main() {
  TestZeroValues();
  TestBoundaryValues();
  TestSmallestValues();
  TestEpsilonValue();
  TestSpecialValueArithmetic();
  TestSpecialValueComparisons();
  TestQuietAndSignalingNaN();
  TestSpecialValueProperties();
  TestUsefulDerivedConstants();
  TestSpecialValueCreation();
  TestEdgeCasesWithAssertions();
  TestNaNBehavior();
  TestInfinityBehavior();
  TestStaticConstantConsistency();
}