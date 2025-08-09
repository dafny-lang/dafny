// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

// Test for fp64 additional special values
// Tests special constants like PositiveZero, NegativeZero, MaxValue, MinValue, etc.

method TestZeroValues() {
  // Test positive and negative zero constants
  var pos_zero := fp64.PositiveZero;
  var neg_zero := fp64.NegativeZero;

  // Test literal zeros
  var lit_pos_zero: fp64 := 0.0;
  var lit_neg_zero: fp64 := -0.0;

  // Verify zeros are equal but have different signs
  assert pos_zero != neg_zero;
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
  var pos_zero := fp64.PositiveZero;
  var neg_zero := fp64.NegativeZero;

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
  // TODO: Add wellformedness checks!
  var nan_created1 := fp64.PositiveInfinity - fp64.PositiveInfinity;
  var nan_created2 := fp64.Sqrt(-1.0);
  assert nan_created1.IsNaN;
  assert nan_created2.IsNaN;

  // Create negative zero
  var neg_zero_created: fp64 := -0.0;  // Explicit type needed for .IsZero/.IsNegative
  assert neg_zero_created.IsZero;
  assert neg_zero_created.IsNegative;
}

method TestEdgeCasesWithAssertions() {
  // Special values
  var nan: fp64 := fp64.NaN;
  var posInf: fp64 := fp64.PositiveInfinity;
  var negInf: fp64 := fp64.NegativeInfinity;
  var posZero: fp64 := 0.0;
  var negZero: fp64 := -0.0;

  // Smallest positive normal number
  var minNormal: fp64 := ~2.2250738585072014e-308;  // 2^(-1022)

  // Smallest positive subnormal number
  var minSubnormal: fp64 := ~4.9406564584124654e-324;  // 2^(-1074) - approximate!

  // Largest finite number
  var maxValue: fp64 := ~1.7976931348623157e308;  // (2-2^(-52))*2^1023

  // Values close to 1.0
  var nextUp1: fp64 := ~1.0000000000000002;  // 1 + 2^(-52)
  var nextDown1: fp64 := ~0.9999999999999999;  // 1 - 2^(-53)

  // Machine epsilon (difference between 1.0 and next representable number)
  var epsilon: fp64 := ~2.220446049250313e-16;  // 2^(-52)

  // Test classification predicates on edge cases
  assert !nan.IsFinite;
  assert nan.IsNaN;

  assert !posInf.IsFinite;
  assert posInf.IsInfinite;
  assert posInf.IsPositive;

  assert !negInf.IsFinite;
  assert negInf.IsInfinite;
  assert negInf.IsNegative;

  assert posZero.IsZero;
  assert posZero.IsFinite;
  assert !posZero.IsNegative;

  assert negZero.IsZero;
  assert negZero.IsFinite;
  assert negZero.IsNegative;

  assert minNormal.IsNormal;
  assert minNormal.IsFinite;
  assert minNormal.IsPositive;

  assert minSubnormal.IsSubnormal;
  assert minSubnormal.IsFinite;
  assert minSubnormal.IsPositive;

  assert maxValue.IsNormal;
  assert maxValue.IsFinite;
  assert maxValue.IsPositive;
}

method TestSignedZero() {
  // Test signed zero behavior
  var posZero: fp64 := 0.0;
  var negZero: fp64 := -0.0;

  // IEEE 754 requires +0 and -0 to compare equal
  assert fp64.Equal(posZero, negZero);

  // But they have different sign bits
  assert posZero.IsZero && !posZero.IsNegative;
  assert negZero.IsZero && negZero.IsNegative;

  // Division by zero produces infinity with the sign of the dividend
  var posInf: fp64 := fp64.PositiveInfinity;
  var negInf: fp64 := fp64.NegativeInfinity;

  // Division by zero is not allowed in Dafny - these would result in infinities in IEEE 754
  // but Dafny's fp64 division has a precondition that divisor != 0
  // ghost var divByPosZero := 1.0 / posZero;  // Would be +∞ in IEEE 754
  // ghost var divByNegZero := 1.0 / negZero;  // Would be -∞ in IEEE 754

  // ghost var negDivByPosZero := -1.0 / posZero;  // Would be -∞ in IEEE 754
  // ghost var negDivByNegZero := -1.0 / negZero;  // Would be +∞ in IEEE 754
}

method TestDetailedSubnormalNumbers() {
  // Test subnormal number behavior
  var minSubnormal: fp64 := ~4.9406564584124654e-324;  // Smallest positive subnormal - approximate!
  var maxSubnormal: fp64 := ~2.2250738585072009e-308;  // Largest subnormal - approximate!
  var minNormal: fp64 := ~2.2250738585072014e-308;     // Smallest normal

  // Classification
  assert minSubnormal.IsSubnormal;
  assert maxSubnormal.IsSubnormal;
  assert minNormal.IsNormal;

  // Subnormal numbers are still finite
  assert minSubnormal.IsFinite;
  assert maxSubnormal.IsFinite;

  // Subnormal numbers have reduced precision but maintain sign
  assert minSubnormal.IsPositive;
  assert (-minSubnormal).IsNegative;
}

method TestNaNBehavior() {
  // Test NaN behavior
  var nan: fp64 := fp64.NaN;
  var x: fp64 := 1.0;

  // NaN propagation in arithmetic - all produce NaN
  ghost var nanPlusX := nan + x;
  assert nanPlusX.IsNaN;  // NaN + anything = NaN

  ghost var nanMinusX := nan - x;
  assert nanMinusX.IsNaN;  // NaN - anything = NaN

  ghost var nanTimesX := nan * x;
  assert nanTimesX.IsNaN;  // NaN * anything = NaN

  ghost var nanDivX := nan / x;
  assert nanDivX.IsNaN;  // NaN / anything = NaN

  ghost var xDivNan := x / nan;
  assert xDivNan.IsNaN;  // anything / NaN = NaN

  // NaN comparisons - all return false
  ghost var nanLessX := nan < x;
  assert !nanLessX;  // NaN < anything = false

  ghost var nanGreaterX := nan > x;
  assert !nanGreaterX;  // NaN > anything = false

  ghost var nanLessEqX := nan <= x;
  assert !nanLessEqX;  // NaN <= anything = false

  ghost var nanGreaterEqX := nan >= x;
  assert !nanGreaterEqX;  // NaN >= anything = false

  // NaN equality per IEEE 754
  ghost var nanEqualNan := fp64.Equal(nan, nan);
  assert !nanEqualNan;  // NaN != NaN per IEEE 754

  ghost var nanEqualX := fp64.Equal(nan, x);
  assert !nanEqualX;  // NaN != anything

  // Also test comparisons with NaN on the right
  assert !(x < nan);   // anything < NaN = false
  assert !(x > nan);   // anything > NaN = false
  assert !(x <= nan);  // anything <= NaN = false
  assert !(x >= nan);  // anything >= NaN = false
}

method TestInfinityBehavior() {
  // Test infinity behavior
  var posInf: fp64 := fp64.PositiveInfinity;
  var negInf: fp64 := fp64.NegativeInfinity;
  var x: fp64 := 1.0;

  // Arithmetic with positive infinity
  ghost var posInfPlusX := posInf + x;
  assert posInfPlusX.IsInfinite && posInfPlusX.IsPositive;  // +∞ + finite = +∞

  ghost var posInfMinusX := posInf - x;
  assert posInfMinusX.IsInfinite && posInfMinusX.IsPositive;  // +∞ - finite = +∞

  ghost var posInfTimesX := posInf * x;
  assert posInfTimesX.IsInfinite && posInfTimesX.IsPositive;  // +∞ * positive = +∞

  ghost var posInfTimesNegX := posInf * -x;
  assert posInfTimesNegX.IsInfinite && posInfTimesNegX.IsNegative;  // +∞ * negative = -∞

  ghost var posInfDivX := posInf / x;
  assert posInfDivX.IsInfinite && posInfDivX.IsPositive;  // +∞ / positive = +∞

  ghost var xDivPosInf := x / posInf;
  assert xDivPosInf.IsZero && !xDivPosInf.IsNegative;  // finite / +∞ = +0

  // Arithmetic with negative infinity
  ghost var negInfPlusX := negInf + x;
  assert negInfPlusX.IsInfinite && negInfPlusX.IsNegative;  // -∞ + finite = -∞

  ghost var negInfMinusX := negInf - x;
  assert negInfMinusX.IsInfinite && negInfMinusX.IsNegative;  // -∞ - finite = -∞

  ghost var negInfTimesX := negInf * x;
  assert negInfTimesX.IsInfinite && negInfTimesX.IsNegative;  // -∞ * positive = -∞

  ghost var negInfTimesNegX := negInf * -x;
  assert negInfTimesNegX.IsInfinite && negInfTimesNegX.IsPositive;  // -∞ * negative = +∞

  ghost var negInfDivX := negInf / x;
  assert negInfDivX.IsInfinite && negInfDivX.IsNegative;  // -∞ / positive = -∞

  ghost var xDivNegInf := x / negInf;
  assert xDivNegInf.IsZero && xDivNegInf.IsNegative;  // positive / -∞ = -0

  // Special cases that produce NaN
  ghost var posInfMinusPosInf := posInf - posInf;
  assert posInfMinusPosInf.IsNaN;  // ∞ - ∞ = NaN

  ghost var posInfDivPosInf := posInf / posInf;
  assert posInfDivPosInf.IsNaN;  // ∞ / ∞ = NaN

  ghost var zeroTimesPosInf := 0.0 * posInf;
  assert zeroTimesPosInf.IsNaN;  // 0 * ∞ = NaN

  ghost var negInfPlusInf := negInf + posInf;
  assert negInfPlusInf.IsNaN;  // -∞ + ∞ = NaN

  ghost var zeroTimesNegInf := 0.0 * negInf;
  assert zeroTimesNegInf.IsNaN;  // 0 * -∞ = NaN

  // Special cases that produce infinity
  ghost var posInfTimesPosInf := posInf * posInf;
  assert posInfTimesPosInf.IsInfinite && posInfTimesPosInf.IsPositive;  // +∞ * +∞ = +∞

  ghost var posInfTimesNegInf := posInf * negInf;
  assert posInfTimesNegInf.IsInfinite && posInfTimesNegInf.IsNegative;  // +∞ * -∞ = -∞

  ghost var negInfTimesNegInf := negInf * negInf;
  assert negInfTimesNegInf.IsInfinite && negInfTimesNegInf.IsPositive;  // -∞ * -∞ = +∞

  // Comparisons with infinity
  assert posInf > x;       // +∞ > any finite
  assert negInf < x;       // -∞ < any finite
  assert posInf > negInf;  // +∞ > -∞
}

method TestRoundingBehavior() {
  // Test rounding behavior
  var x: fp64 := ~1.1;  // Not exactly representable in binary
  var y: fp64 := ~1.1;  // Same value

  // IEEE 754 guarantees that the same decimal value rounds to the same binary representation
  assert fp64.Equal(x, y);

  // Values that demonstrate rounding
  var a: fp64 := ~0.1;                  // Not exactly representable in binary
  var b: fp64 := ~0.2;                  // Not exactly representable in binary
  var c: fp64 := ~0.3;                  // Not exactly representable in binary

  // This would fail with exact equality due to rounding errors
  // assert a + b == c;  // This would fail

  // But the values should be close
  ghost var diff := (a + b) - c;       // Should be very small but non-zero
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
  TestDetailedSubnormalNumbers();
  TestNaNBehavior();
  TestInfinityBehavior();
  TestRoundingBehavior();
}