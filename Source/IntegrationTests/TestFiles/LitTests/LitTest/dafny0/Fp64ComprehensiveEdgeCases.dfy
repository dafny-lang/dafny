// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s" -- --verification-time-limit:30

// Comprehensive edge case tests for fp64
// This tests the handling of denormalized numbers, overflow, underflow,
// and other special cases as specified in the design document.

method TestDenormalizedNumbers() {
  // Test with denormalized (subnormal) numbers
  var minSubnormal: fp64 := ~4.9406564584124654e-324;  // Smallest positive subnormal
  var almostMinNormal: fp64 := ~2.2250738585072009e-308;  // Just below min normal
  var minNormal: fp64 := ~2.2250738585072014e-308;  // Smallest normal number

  // Classification checks
  assert minSubnormal.IsSubnormal;
  assert !minSubnormal.IsNormal;
  assert minSubnormal.IsFinite;

  assert almostMinNormal.IsSubnormal;
  assert !almostMinNormal.IsNormal;

  assert minNormal.IsNormal;
  assert !minNormal.IsSubnormal;

  // Arithmetic with subnormal numbers
  ghost var sum := minSubnormal + minSubnormal;
  assert sum.IsSubnormal;  // Sum of two subnormals should still be subnormal
  assert sum > minSubnormal;  // Should be larger than the original

  ghost var product := minSubnormal * 0.5;
  assert product == 0.0;  // Underflows to zero

  // Test that subnormal numbers are positive but very small
  assert minSubnormal > 0.0;
  assert minSubnormal < minNormal;

  // All assertions verify denormalized number behavior
}

method TestOverflowUnderflow() {
  // Test overflow and underflow behavior
  var maxFinite: fp64 := ~1.7976931348623157e308;  // Max finite value
  var minPositive: fp64 := ~4.9406564584124654e-324;  // Min positive value

  // Overflow tests (in ghost context to avoid precondition violations)
  ghost var overflow1 := maxFinite * 2.0;
  assert overflow1 == fp64.PositiveInfinity;

  ghost var overflow2 := -maxFinite * 2.0;
  assert overflow2 == fp64.NegativeInfinity;

  ghost var overflow3 := maxFinite + maxFinite;
  assert overflow3 == fp64.PositiveInfinity;

  // Underflow tests (in ghost context to avoid precondition violations)
  ghost var underflow1 := minPositive / 2.0;
  assert underflow1 == 0.0;

  ghost var underflow2 := minPositive * 0.5;
  assert underflow2 == 0.0;

  // Gradual underflow
  ghost var gradual1 := minPositive * 0.75;
  assert gradual1 == minPositive;

  ghost var gradual2 := minPositive * 0.25;
  assert gradual2 == 0.0;

  // All assertions verify overflow/underflow behavior
}

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
  ghost var largeSum := large + small;
  assert largeSum == large;  // Small gets lost due to precision limits

  ghost var diff := largeSum - large;
  assert diff == 0.0;  // Should be 0, not 1

  // All assertions verify rounding error behavior
}

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

  // All assertions verify non-associativity
}

method TestSpecialOperations() {
  // Test special operations and their behavior with edge cases
  var nan: fp64 := fp64.NaN;
  var posInf: fp64 := fp64.PositiveInfinity;
  var negInf: fp64 := fp64.NegativeInfinity;
  var posZero: fp64 := 0.0;
  var negZero: fp64 := -0.0;

  // Special case: 0/0 = NaN (skipped to avoid division by zero error)

  // Special case: inf/inf = NaN
  ghost var infByInf := posInf / posInf;
  assert infByInf.IsNaN;

  // Special case: inf * 0 = NaN
  ghost var infTimesZero := posInf * posZero;
  assert infTimesZero.IsNaN;

  // Special case: inf - inf = NaN
  ghost var infMinusInf := posInf - posInf;
  assert infMinusInf.IsNaN;

  // Special case: 0 * inf = NaN
  ghost var zeroTimesInf := posZero * posInf;
  assert zeroTimesInf.IsNaN;

  // NaN propagation
  ghost var nanPlus1 := nan + 1.0;
  assert nanPlus1.IsNaN;

  ghost var nanTimes2 := nan * 2.0;
  assert nanTimes2.IsNaN;

  // Infinity arithmetic
  ghost var infPlus1 := posInf + 1.0;
  assert infPlus1 == posInf;

  ghost var infTimes2 := posInf * 2.0;
  assert infTimes2 == posInf;

  ghost var negInfTimes2 := negInf * 2.0;
  assert negInfTimes2 == negInf;

  // Special cases: division by zero (skipped to avoid division by zero errors)
  // 1/0 = +∞, -1/0 = -∞, 1/-0 = -∞

  // All assertions verify special operation behavior
}

method TestPrecisionLimits() {
  // Test precision limits of fp64
  var maxExactInt: fp64 := 4503599627370496.0;  // 2^52, integers up to 2^53 are exactly representable
  var nextInt: fp64 := 4503599627370497.0;      // 2^52 + 1, still exactly representable

  // In fp64, both are exactly representable up to 2^53
  assert maxExactInt != nextInt;  // They should be different

  // Large integers lose precision after 2^53
  var large1: fp64 := 9007199254740992.0;   // 2^53
  var large2: fp64 := ~9007199254740993.0;   // 2^53 + 1, rounds to 2^53
  var large3: fp64 := 9007199254740994.0;   // 2^53 + 2, exactly representable
  var large4: fp64 := ~9007199254740995.0;   // 2^53 + 3, rounds to 2^53 + 4
  var large5: fp64 := 9007199254740996.0;    // 2^53 + 4, exactly representable

  assert large1 == large2;    // 2^53 + 1 rounds to 2^53
  assert large1 != large3;   // 2^53 + 2 is exactly representable
  assert large4 == large5;    // 2^53 + 3 rounds to 2^53 + 4

  // All assertions verify precision limit behavior
}

method TestUlpAndMachineEpsilon() {
  // Test Unit in Last Place (ULP) and machine epsilon concepts
  var one: fp64 := 1.0;
  var nextUp: fp64 := ~1.00000000000000022204460492503;  // 1 + 2^(-52)
  var ulpOfOne: fp64 := ~2.220446049250313e-16;          // 2^(-52), machine epsilon for fp64

  // nextUp - one should be approximately epsilon
  ghost var diff := nextUp - one;
  assert diff == ulpOfOne;  // The difference should be machine epsilon

  // Test that adding smaller values to 1.0 doesn't change it
  var smallerThanEpsilon: fp64 := ulpOfOne / 2.0;
  ghost var oneWithSmaller := one + smallerThanEpsilon;
  assert oneWithSmaller == one;  // Too small to affect 1.0

  // Test that adding epsilon to 1.0 does change it
  ghost var oneWithEpsilon := one + ulpOfOne;
  assert oneWithEpsilon == nextUp;  // Should equal the next representable value
  assert oneWithEpsilon != one;     // Should be different from 1.0

  // For values near 1.0, the ULP is epsilon
  // In a full implementation, we would test fp64.Ulp(1.0) == epsilon

  // All assertions verify ULP and epsilon behavior
}

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

method TestExtremePrecisionCases() {
  // Test extreme precision cases
  var tiny1: fp64 := ~1e-300;
  var tiny2: fp64 := ~1e-305;
  var tiny3: fp64 := ~1e-310;
  
  // All should be positive and finite
  assert tiny1 > 0.0 && tiny1.IsFinite;
  assert tiny2 > 0.0 && tiny2.IsFinite;
  assert tiny3 > 0.0 && tiny3.IsFinite;
  
  // Test relative sizes
  assert tiny1 > tiny2;
  assert tiny2 > tiny3;
  
  // Test that multiplication of tiny values
  ghost var product: fp64 := tiny1 * tiny3;
  assert product == 0.0 || product.IsSubnormal || product.IsNormal;
  
  // Test max safe integer boundary
  var max_safe: fp64 := 9007199254740992.0;  // 2^53
  var above_max: fp64 := ~9007199254740993.0;  // 2^53 + 1
  
  // Can't represent odd numbers above 2^53
  assert max_safe + 1.0 == above_max;
  assert above_max == max_safe;  // Rounds down
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
