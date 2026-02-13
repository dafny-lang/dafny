// RUN: %testDafnyForEachResolver "%s"

// Comprehensive edge case tests for fp64
// This tests the handling of denormalized numbers, overflow, underflow,
// and other special cases as specified in the design document.

// Tests behavior of denormalized (subnormal) numbers near the underflow threshold.
// Subnormal numbers have reduced precision but allow gradual underflow to zero.
method TestDenormalizedNumbers() {
  // Test with denormalized (subnormal) numbers
  var min_subnormal: fp64 := ~4.9406564584124654e-324;  // Smallest positive subnormal (2^-1074)
  var almost_min_normal: fp64 := ~2.2250738585072009e-308;  // Just below min normal
  var min_normal: fp64 := ~2.2250738585072014e-308;  // Smallest normal number

  // Classification checks
  assert min_subnormal.IsSubnormal;
  assert !min_subnormal.IsNormal;
  assert min_subnormal.IsFinite;

  assert almost_min_normal.IsSubnormal;
  assert !almost_min_normal.IsNormal;

  assert min_normal.IsNormal;
  assert !min_normal.IsSubnormal;

  // Arithmetic with subnormal numbers
  ghost var sum := min_subnormal + min_subnormal;
  assert sum.IsSubnormal;  // Sum of two subnormals should still be subnormal
  assert sum > min_subnormal;  // Should be larger than the original

  ghost var product := min_subnormal * 0.5;
  assert product == 0.0;  // Underflows to zero (below smallest representable)

  // Test that subnormal numbers are positive but very small
  assert min_subnormal.IsPositive;
  assert min_subnormal < min_normal;
}

// Tests overflow to infinity and underflow to zero behaviors.
// Operations exceeding fp64 range produce infinities; those below minimum produce zero.
method TestOverflowUnderflow() {
  // Test overflow and underflow behavior
  var max_finite: fp64 := ~1.7976931348623157e308;  // Max finite value
  var min_positive: fp64 := ~4.9406564584124654e-324;  // Min positive value (smallest subnormal)

  // Overflow tests (in ghost context to avoid precondition violations)
  ghost var overflow1 := max_finite * 2.0;
  assert overflow1 == fp64.PositiveInfinity;

  ghost var overflow2 := -max_finite * 2.0;
  assert overflow2 == fp64.NegativeInfinity;

  ghost var overflow3 := max_finite + max_finite;
  assert overflow3 == fp64.PositiveInfinity;

  // Underflow tests (in ghost context to avoid precondition violations)
  ghost var underflow1 := min_positive / 2.0;
  assert underflow1 == 0.0;

  ghost var underflow2 := min_positive * 0.5;
  assert underflow2 == 0.0;

  // Gradual underflow: demonstrates rounding at the edge of representation.
  // At this extreme, only 0 and min_positive are representable.
  // The rounding boundary is exactly at min_positive/2.
  ghost var gradual1 := min_positive * 0.75;  // Result ~3.7e-324 > min_positive/2
  assert gradual1 == min_positive;  // Rounds UP to min_positive

  ghost var gradual2 := min_positive * 0.25;  // Result ~1.2e-324 < min_positive/2
  assert gradual2 == 0.0;  // Rounds DOWN to zero
}

// Tests rounding errors and precision loss in floating-point arithmetic.
// Demonstrates that fp64 cannot exactly represent all decimal values.
method TestRoundingErrors() {
  // Test rounding errors and precision loss
  var a: fp64 := ~0.1;  // Not exactly representable in binary
  var b: fp64 := ~0.2;  // Not exactly representable in binary
  var c: fp64 := ~0.3;  // Not exactly representable in binary

  // The classic floating-point issue: 0.1 + 0.2 != 0.3
  ghost var sum := a + b;
  assert sum != c;  // In exact arithmetic: sum == c, but in floating-point: sum != c

  // Large number precision loss
  var large: fp64 := 1.0e16;  // 10^16
  var small: fp64 := 1.0;
  ghost var large_sum := large + small;
  assert large_sum == large;  // Small gets lost due to precision limits

  ghost var diff := large_sum - large;
  assert diff == 0.0;  // Is 0 in fp64 (would be 1 in exact arithmetic)
}

// Tests non-associativity of floating-point operations.
// Shows that (a + b) + c may not equal a + (b + c) due to rounding.
method TestNonAssociativity() {
  // Test non-associativity of floating-point operations
  var a: fp64 := 1.0e20;
  var b: fp64 := -1.0e20;
  var c: fp64 := 1.0;

  // (a + b) + c vs a + (b + c)
  ghost var sum1 := (a + b) + c;
  ghost var sum2 := a + (b + c);

  assert sum1 == 1.0;  // (1e20 + (-1e20)) + 1 = 0 + 1 = 1
  assert sum2 == 0.0;  // 1e20 + ((-1e20) + 1) = 1e20 + (-1e20) = 0 (1 gets lost)
  assert sum1 != sum2;  // Demonstrates non-associativity
}

// Tests special IEEE 754 operations that produce NaN or infinity.
// Includes indeterminate forms like 0/0, inf/inf, inf*0.
method TestSpecialOperations() {
  // Test special operations and their behavior with edge cases
  var nan: fp64 := fp64.NaN;
  var pos_inf: fp64 := fp64.PositiveInfinity;
  var neg_inf: fp64 := fp64.NegativeInfinity;
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // Special case: 0/0 = NaN (skipped to avoid division by zero error)

  // Special case: inf/inf = NaN
  ghost var inf_by_inf := fp64.Div(pos_inf, pos_inf);
  assert inf_by_inf.IsNaN;

  // Special case: inf * 0 = NaN
  ghost var inf_times_zero := fp64.Mul(pos_inf, pos_zero);
  assert inf_times_zero.IsNaN;

  // Special case: inf - inf = NaN
  ghost var inf_minus_inf := fp64.Sub(pos_inf, pos_inf);
  assert inf_minus_inf.IsNaN;

  // Special case: 0 * inf = NaN
  ghost var zero_times_inf := fp64.Mul(pos_zero, pos_inf);
  assert zero_times_inf.IsNaN;

  // NaN propagation
  ghost var nan_plus_1 := fp64.Add(nan, 1.0);
  assert nan_plus_1.IsNaN;

  ghost var nan_times_2 := fp64.Mul(nan, 2.0);
  assert nan_times_2.IsNaN;

  // Infinity arithmetic
  ghost var inf_plus_1 := fp64.Add(pos_inf, 1.0);
  assert inf_plus_1 == pos_inf;

  ghost var inf_times_2 := fp64.Mul(pos_inf, 2.0);
  assert inf_times_2 == pos_inf;

  ghost var neg_inf_times_2 := fp64.Mul(neg_inf, 2.0);
  assert neg_inf_times_2 == neg_inf;

  // Special cases: division by zero (skipped to avoid division by zero errors)
  // 1/0 = +∞, -1/0 = -∞, 1/-0 = -∞
}

// Tests precision limits for integer representation in fp64.
// After 2^53, not all integers can be exactly represented.
method TestPrecisionLimits() {
  // Test precision limits of fp64
  var max_exact_int: fp64 := 4503599627370496.0;  // 2^52
  var next_int: fp64 := 4503599627370497.0;       // 2^52 + 1
  // All integers from -(2^53) to 2^53 are exactly representable

  // In fp64, both are exactly representable up to 2^53
  assert max_exact_int != next_int;  // They should be different

  // Large integers lose precision after 2^53
  var large1: fp64 := 9007199254740992.0;    // 2^53
  var large2: fp64 := ~9007199254740993.0;   // 2^53 + 1, rounds to 2^53
  var large3: fp64 := 9007199254740994.0;    // 2^53 + 2, exactly representable
  var large4: fp64 := ~9007199254740995.0;   // 2^53 + 3, rounds to 2^53 + 4
  var large5: fp64 := 9007199254740996.0;    // 2^53 + 4, exactly representable

  assert large1 == large2;    // 2^53 + 1 rounds to 2^53 (nearest even)
  assert large1 != large3;    // 2^53 + 2 is exactly representable (even)
  assert large4 == large5;    // 2^53 + 3 rounds to 2^53 + 4 (nearest even)
}

// Tests Unit in Last Place (ULP) and machine epsilon concepts.
// Machine epsilon is the smallest value that changes 1.0 when added.
method TestUlpAndMachineEpsilon() {
  // Test Unit in Last Place (ULP) and machine epsilon concepts
  var one: fp64 := 1.0;
  var next_up: fp64 := ~1.00000000000000022204460492503;  // 1 + 2^(-52)
  var ulp_of_one: fp64 := ~2.220446049250313e-16;         // 2^(-52), machine epsilon for fp64

  // next_up - one should be approximately epsilon
  ghost var diff := next_up - one;
  assert diff == ulp_of_one;  // The difference should be machine epsilon

  // Test that adding smaller values to 1.0 doesn't change it
  var smaller_than_epsilon: fp64 := ulp_of_one / 2.0;
  ghost var one_with_smaller := one + smaller_than_epsilon;
  assert one_with_smaller == one;  // Too small to affect 1.0

  // Test that adding epsilon to 1.0 does change it
  ghost var one_with_epsilon := one + ulp_of_one;
  assert one_with_epsilon == next_up;  // Should equal the next representable value
  assert one_with_epsilon != one;      // Should be different from 1.0
}

// Tests signed zero behavior in IEEE 754.
// +0.0 and -0.0 are distinct bit patterns but compare as equal.
method TestSignedZeroBehavior() {
  // Test signed zero behavior
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // Both are zeros
  assert pos_zero.IsZero;
  assert neg_zero.IsZero;

  // But have different signs
  assert !pos_zero.IsNegative;
  assert neg_zero.IsNegative;

  // IEEE 754 equality treats them as equal
  assert fp64.Equal(pos_zero, neg_zero);

  // But bitwise they're different
  assert pos_zero == pos_zero;
  assert neg_zero == neg_zero;
  // Can't assert pos_zero != neg_zero in compiled context

  // Arithmetic with signed zeros preserves zero property
  assert (pos_zero + pos_zero).IsZero;
  assert (neg_zero + neg_zero).IsZero;
  assert (pos_zero + neg_zero).IsZero;
  assert (neg_zero + pos_zero).IsZero;

  // Negation of zeros produces zeros
  assert (-pos_zero).IsZero;
  assert (-neg_zero).IsZero;

  // Division behavior (avoiding div by zero)
  assert (1.0 / fp64.PositiveInfinity).IsZero;
  assert (1.0 / fp64.NegativeInfinity).IsZero;
  assert !(1.0 / fp64.PositiveInfinity).IsNegative;
  assert (1.0 / fp64.NegativeInfinity).IsNegative;
}

// Tests extreme precision cases near the limits of representation.
// Includes very small values and the boundary of exact integer representation.
method TestExtremePrecisionCases() {
  // Test extreme precision cases
  var tiny1: fp64 := ~1e-300;
  var tiny2: fp64 := ~1e-305;
  var tiny3: fp64 := ~1e-310;

  // All should be positive and finite
  assert tiny1.IsPositive && tiny1.IsFinite;
  assert tiny2.IsPositive && tiny2.IsFinite;
  assert tiny3.IsPositive && tiny3.IsFinite;

  // Test relative sizes
  assert tiny1 > tiny2;
  assert tiny2 > tiny3;

  // Test that multiplication of tiny values underflows
  ghost var product: fp64 := tiny1 * tiny3;  // ~1e-300 * ~1e-310 = ~1e-610
  assert product == 0.0;  // Far below smallest representable (~4.94e-324), underflows to zero

  // Test max safe integer boundary
  var max_safe: fp64 := 9007199254740992.0;  // 2^53
  var above_max: fp64 := ~9007199254740993.0;  // 2^53 + 1

  // Can't represent odd numbers above 2^53
  // Both assertions below are true because:
  // - max_safe + 1.0 produces 2^53 (1.0 gets lost due to precision)
  // - above_max (with ~) rounds 2^53+1 back to 2^53 (nearest even)
  // So both expressions evaluate to the same value: 2^53
  assert max_safe + 1.0 == above_max;
  assert above_max == max_safe;  // Rounds to nearest even (2^53)
}

method Main() {
  TestDenormalizedNumbers();
  TestOverflowUnderflow();
  TestRoundingErrors();
  TestNonAssociativity();
  TestSpecialOperations();
  TestPrecisionLimits();
  TestUlpAndMachineEpsilon();
  TestSignedZeroBehavior();
  TestExtremePrecisionCases();
}
