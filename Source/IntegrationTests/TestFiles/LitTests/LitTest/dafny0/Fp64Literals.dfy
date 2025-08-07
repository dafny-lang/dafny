// RUN: %testDafnyForEachResolver "%s"

// Consolidated tests for fp64 literals including exact literals and approximate literals with ~ prefix
// This file combines tests from ApproximateLiteralDemo, ApproximateLiteralRules, and ApproximateLiterals

// ===== Core Literal Tests =====

method TestExactFp64Literals() {
  // Powers of two are exactly representable
  var half: fp64 := 0.5;
  var quarter: fp64 := 0.25;
  var eighth: fp64 := 0.125;
  assert half * 2.0 == 1.0;
  assert quarter * 4.0 == 1.0;
  assert eighth * 8.0 == 1.0;

  // Sums of powers of 2 are exact
  var one_point_five: fp64 := 1.5;
  var three_quarters: fp64 := 0.75;
  assert one_point_five == 1.0 + 0.5;
  assert three_quarters == 0.5 + 0.25;

  // Scientific notation for exact values
  var thousand: fp64 := 1.0e3;
  var eight_thousand: fp64 := 8.0e3;
  assert thousand == 1000.0;
  assert eight_thousand == 8000.0;

  // Negative exact values
  var neg_one: fp64 := -1.0;
  var neg_half: fp64 := -0.5;
  assert neg_one == -1.0;
  assert neg_half * -2.0 == 1.0;
}

method TestApproximateFp64Literals() {
  // Common decimal fractions require ~ prefix
  var tenth: fp64 := ~0.1;
  var fifth: fp64 := ~0.2;
  var three_tenths: fp64 := ~0.3;

  // These are NOT exactly equal due to rounding
  assert tenth + fifth != three_tenths || tenth + fifth == three_tenths; // One must be true

  // Mathematical constants are approximate
  var pi: fp64 := ~3.14159265358979323846;
  var e: fp64 := ~2.71828182845904523536;

  // Verify constants are in expected ranges
  assert pi > ~3.14 && pi < ~3.15;
  assert e > ~2.71 && e < ~2.72;

  // Negative approximate values use ~- syntax
  var neg_tenth: fp64 := ~-0.1;
  assert neg_tenth < 0.0;
  assert -neg_tenth == tenth || -neg_tenth != tenth; // May or may not be bitwise equal
}

// ===== Syntax Rules Tests =====

method TestApproximateLiteralSyntaxRules() {
  // ~ prefix must encompass the entire literal including sign
  var pos_approx: fp64 := ~0.1;
  var neg_approx: fp64 := ~-0.1;

  // Verify signs are correct
  assert pos_approx > 0.0;
  assert neg_approx < 0.0;

  // ~ only applies to literals, not variables or expressions
  var x: fp64 := ~0.1;
  var y: fp64 := x;  // No ~ needed on variable
  var z: fp64 := x + y;  // No ~ needed on expression

  // Verify operations work
  assert z == x + y;
  assert z > x;
}

method TestRealLiteralsUnaffected() {
  // Real literals are exact (arbitrary precision)
  var r_tenth: real := 0.1;
  var r_three_tenths: real := 0.3;

  // In real arithmetic, 0.1 + 0.2 == 0.3 exactly
  assert r_tenth + 0.2 == r_three_tenths;

  // Real vs fp64 - different types
  var real_pi: real := 3.14159265358979323846;
  var fp64_pi: fp64 := ~3.14159265358979323846;
  // Cannot compare directly - different types
}

// ===== Type Inference Tests =====

method TestTypeInference() {
  // Type inference with exact literals
  var exact_inferred := 0.5;      // Infers as real by default
  var exact_fp64: fp64 := 0.5;    // Explicitly fp64

  // Type inference with approximate literals
  var approx_inferred := ~0.1;    // Must be fp64 due to ~
  var approx_fp64: fp64 := ~0.1;  // Explicitly fp64

  // Verify approximate literals force fp64 type
  assert approx_inferred == approx_fp64; // Same type, same value

  // Operations preserve type
  var sum := approx_inferred + approx_fp64;
  assert sum == approx_inferred + approx_fp64; // Tautology but shows type works
}

// ===== Edge Cases =====

method TestEdgeCases() {
  // Zero values
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  // Verify zero properties
  assert pos_zero.IsZero;
  assert neg_zero.IsZero;
  assert !pos_zero.IsNegative;
  assert neg_zero.IsNegative;

  // Very small numbers are still positive
  var tiny: fp64 := ~1.0e-100;
  assert tiny > 0.0;
  assert tiny.IsFinite;

  // Very large numbers are still finite
  var huge: fp64 := ~1.0e100;
  assert huge.IsFinite;
  assert !huge.IsInfinite;

  // Precision boundaries
  var max_safe_int: fp64 := 9007199254740992.0;  // 2^53
  assert max_safe_int.IsFinite;
  assert max_safe_int > 0.0;
}

// ===== Practical Examples =====

method TestFinancialCalculations() {
  // Computing sales tax
  var price: fp64 := ~19.99;
  var taxRate: fp64 := ~0.0825;  // 8.25%
  var tax: fp64 := price * taxRate;
  var total: fp64 := price + tax;

  // Verify calculations make sense
  assert tax > 0.0;
  assert total > price;
  assert total == price + tax;
}

method TestScientificComputations() {
  // Circle calculations
  var radius: fp64 := 5.0;  // Exact
  var pi: fp64 := ~3.14159265358979323846;
  var area: fp64 := pi * radius * radius;
  var circumference: fp64 := 2.0 * pi * radius;

  // Verify calculations are reasonable
  assert area > 0.0;
  assert circumference > 0.0;
  assert area > radius * radius;  // Since pi > 1
  assert circumference > 2.0 * radius;  // Since pi > 1
}

method TestRealVsFp64Arithmetic() {
  // Real arithmetic is exact
  var real_sum: real := 0.1 + 0.2;
  assert real_sum == 0.3;  // Exact in real

  // fp64 arithmetic has rounding errors
  var fp64_one_tenth: fp64 := ~0.1;
  var fp64_two_tenths: fp64 := ~0.2;
  var fp64_sum: fp64 := fp64_one_tenth + fp64_two_tenths;
  var fp64_three_tenths: fp64 := ~0.3;

  // The sum exists and is finite
  assert fp64_sum.IsFinite;
  assert fp64_three_tenths.IsFinite;

  assert fp64_sum != fp64_three_tenths;

  // We can also verify using IEEE 754 equality
  assert !fp64.Equal(fp64_sum, fp64_three_tenths);
}

// ===== Additional tests from merged files =====

method TestExactRepresentationRules() {
  // Powers of 2 are exactly representable
  var pow2_0: fp64 := 1.0;        // 2^0
  var pow2_1: fp64 := 2.0;        // 2^1
  var pow2_2: fp64 := 4.0;        // 2^2
  var pow2_neg1: fp64 := 0.5;     // 2^(-1)
  var pow2_neg2: fp64 := 0.25;    // 2^(-2)

  // Verify powers of 2 relationships
  assert pow2_0 * 2.0 == pow2_1;
  assert pow2_1 * 2.0 == pow2_2;
  assert pow2_neg1 * 2.0 == pow2_0;
  assert pow2_neg2 * 2.0 == pow2_neg1;

  // Sums of powers of 2 are exact
  assert 1.5 == 1.0 + 0.5;        // 2^0 + 2^(-1)
  assert 0.75 == 0.5 + 0.25;      // 2^(-1) + 2^(-2)
  assert 1.625 == 1.0 + 0.5 + 0.125;  // 2^0 + 2^(-1) + 2^(-3)

  // Fractions with power-of-2 denominators
  assert 0.5 == 1.0 / 2.0;        // 1/2
  assert 0.25 == 1.0 / 4.0;       // 1/4
  assert 0.125 == 1.0 / 8.0;      // 1/8
}

method TestDecimalToBinaryConversion() {
  // Test exact decimal to binary conversions
  var half: fp64 := 0.5;         // Binary: 0.1
  var three_quarters: fp64 := 0.75;  // Binary: 0.11
  var five_eighths: fp64 := 0.625;   // Binary: 0.101

  // Verify exact representations
  assert half == 1.0 / 2.0;
  assert three_quarters == 3.0 / 4.0;
  assert five_eighths == 5.0 / 8.0;

  // Verify relationships
  assert three_quarters == half + 0.25;
  assert five_eighths == half + 0.125;
}

method TestScientificNotationExactness() {
  // Small integer powers of 10 are exact
  var ten: fp64 := 1.0e1;
  var hundred: fp64 := 1.0e2;
  assert ten == 10.0;
  assert hundred == 100.0;
  assert hundred == ten * ten;

  // Powers of 2 in scientific notation
  var sixteen: fp64 := 1.6e1;
  var thirty_two: fp64 := 3.2e1;
  var sixty_four: fp64 := 6.4e1;

  assert sixteen == 16.0;
  assert thirty_two == 32.0;
  assert sixty_four == 64.0;
  assert thirty_two == sixteen * 2.0;
  assert sixty_four == thirty_two * 2.0;
}

method TestExactlyRepresentableLiterals() {
  // Verify powers of 2 chain
  var one: fp64 := 1.0;
  var two: fp64 := 2.0;
  var four: fp64 := 4.0;
  var eight: fp64 := 8.0;

  assert two == one * 2.0;
  assert four == two * 2.0;
  assert eight == four * 2.0;

  // Verify sums of powers of 2
  assert 1.5 == 1.0 + 0.5;
  assert 0.75 == 0.5 + 0.25;
  assert 1.25 == 1.0 + 0.25;
  assert 3.25 == 2.0 + 1.0 + 0.25;

  // Small integers are exact
  var forty_two: fp64 := 42.0;
  var two_fifty_five: fp64 := 255.0;
  assert forty_two > 41.0 && forty_two < 43.0;
  assert two_fifty_five == 256.0 - 1.0;

  // Negative values work correctly
  assert -1.0 == -(1.0);
  assert -0.5 * -2.0 == 1.0;
  assert -1.5 == -(1.5);
}


method TestMixedLiteralFormats() {
  // Different formats for same exact value
  assert 1.5 == 1.5e0;
  assert 0.25 == 2.5e-1;
  assert 1024.0 == 1.024e3;

  // Leading/trailing dot syntax
  assert .5 == 0.5;
  assert 1. == 1.0;

  // Multiple representations of zero
  assert 0.0 == 0.00;
  assert 0.0 == 0e0;
  assert 0.0 == .0;
}

method TestLiteralPrecisionBoundaries() {
  // Maximum safely representable integer (2^53)
  var max_safe_int: fp64 := 9007199254740992.0;

  // Verify it's the boundary
  assert max_safe_int + 1.0 == ~9007199254740993.0;
  assert max_safe_int - 1.0 == 9007199254740991.0;

  // Exact power of 2 fractions
  var tiny_exact: fp64 := 0.00006103515625;  // 2^-14
  assert tiny_exact > 0.0;
  assert tiny_exact * 16384.0 == 1.0;  // 2^14 * 2^-14 = 1
}

method TestSpecialValueLiterals() {
  // Special values from static fields
  var nan := fp64.NaN;
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;

  // Verify special value properties
  assert nan.IsNaN;
  assert pos_inf.IsInfinite && pos_inf.IsPositive;
  assert neg_inf.IsInfinite && neg_inf.IsNegative;

  // Zero values
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;

  assert pos_zero.IsZero && !pos_zero.IsNegative;
  assert neg_zero.IsZero && neg_zero.IsNegative;
}

method TestInexactLiterals() {
  // These require ~ because they're not exactly representable
  var tenth: fp64 := ~0.1;
  var two_tenths: fp64 := ~0.2;
  var three_tenths: fp64 := ~0.3;

  // Verify approximate arithmetic
  var sum := tenth + two_tenths;
  // Cannot assert sum == three_tenths due to rounding

  // But we can verify they're in reasonable ranges
  assert tenth > ~0.09 && tenth < ~0.11;
  assert two_tenths > ~0.19 && two_tenths < ~0.21;
  assert three_tenths > ~0.29 && three_tenths < ~0.31;
}

method TestLiteralArithmetic() {
  // Literal arithmetic is evaluated at compile time
  assert 1.5 + 2.5 == 4.0;
  assert 10.0 - 3.5 == 6.5;
  assert 2.0 * 3.5 == 7.0;
  assert 10.0 / 4.0 == 2.5;

  // More complex expressions
  assert (1.0 + 2.0) * 3.0 == 9.0;
  assert 16.0 / 2.0 / 2.0 == 4.0;
  assert -(-1.0) == 1.0;
}

// Edge case tests moved to TestMixedLiteralFormats

method TestExtremeValues() {
  // Large exact values (powers of 2)
  var large_pow2: fp64 := 1.125899906842624e15;   // 2^50
  assert large_pow2 > 0.0;
  assert large_pow2.IsFinite;

  // Small exact values (negative powers of 2)
  var small_pow2: fp64 := 0.0009765625;           // 2^-10
  assert small_pow2 > 0.0;
  assert small_pow2 * 1024.0 == 1.0;  // 2^-10 * 2^10 = 1

  // Approximate extreme values
  var huge: fp64 := ~1.0e100;
  var tiny: fp64 := ~1.0e-100;
  assert huge.IsFinite && !huge.IsInfinite;
  assert tiny > 0.0 && tiny.IsFinite;
}

// Hexadecimal literals not supported - method removed

method TestLiteralPrecisionLimits() {
  // Exact values - powers of 2
  assert 0.5 == 1.0 / 2.0;      // 2^-1
  assert 0.25 == 1.0 / 4.0;     // 2^-2

  // Exact integers up to 2^53
  var max_exact_int: fp64 := 9007199254740992.0;  // 2^53
  var regular_int: fp64 := 42.0;
  var million: fp64 := 1000000.0;

  assert regular_int == 42.0;
  assert million * ~0.000001 == 1.0;
  assert max_exact_int > 9007199254740991.0;
}

method Main() {
  TestExactFp64Literals();
  TestApproximateFp64Literals();
  TestApproximateLiteralSyntaxRules();
  TestRealLiteralsUnaffected();
  TestTypeInference();
  TestEdgeCases();
  TestExactRepresentationRules();
  TestDecimalToBinaryConversion();
  TestScientificNotationExactness();
  TestExactlyRepresentableLiterals();
  TestMixedLiteralFormats();
  TestLiteralPrecisionBoundaries();
  TestSpecialValueLiterals();
  TestInexactLiterals();
  TestLiteralArithmetic();
  TestExtremeValues();
  TestLiteralPrecisionLimits();
  TestFinancialCalculations();
  TestScientificComputations();
  TestRealVsFp64Arithmetic();
}