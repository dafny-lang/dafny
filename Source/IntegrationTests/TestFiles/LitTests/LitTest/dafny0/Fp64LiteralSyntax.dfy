// RUN: %testDafnyForEachResolver "%s"

// Tests for fp64 literal syntax, including exact literals, approximate literals with ~ prefix,
// type inference, and practical usage examples

// ===== Core Literal Tests =====

method TestExactFp64Literals() {
  // Powers of two are exactly representable
  var half: fp64 := 0.5;         // Binary: 0.1
  var quarter: fp64 := 0.25;     // Binary: 0.01
  var eighth: fp64 := 0.125;     // Binary: 0.001
  assert half * 2.0 == 1.0;
  assert quarter * 4.0 == 1.0;
  assert eighth * 8.0 == 1.0;

  // Division forms are also exact
  assert 0.5 == 1.0 / 2.0;        // 1/2
  assert 0.25 == 1.0 / 4.0;       // 1/4
  assert 0.125 == 1.0 / 8.0;      // 1/8

  // Sums of powers of 2 are exact
  var one_point_five: fp64 := 1.5;       // Binary: 1.1
  var three_quarters: fp64 := 0.75;      // Binary: 0.11
  var five_eighths: fp64 := 0.625;       // Binary: 0.101
  assert one_point_five == 1.0 + 0.5;
  assert three_quarters == 0.5 + 0.25;
  assert five_eighths == 0.5 + 0.125;
  assert 1.625 == 1.0 + 0.5 + 0.125;  // 2^0 + 2^(-1) + 2^(-3)

  // Small integers are exactly representable
  var forty_two: fp64 := 42.0;
  var two_fifty_five: fp64 := 255.0;
  assert forty_two > 41.0 && forty_two < 43.0;
  assert two_fifty_five == 256.0 - 1.0;

  // Scientific notation for exact values
  var thousand: fp64 := 1.0e3;
  var eight_thousand: fp64 := 8.0e3;
  assert thousand == 1000.0;
  assert eight_thousand == 8000.0;

  // Powers of 2 in scientific notation
  var sixteen: fp64 := 1.6e1;
  var thirty_two: fp64 := 3.2e1;
  assert sixteen == 16.0;
  assert thirty_two == 32.0;
  assert thirty_two == sixteen * 2.0;

  // Negative exact values
  var neg_one: fp64 := -1.0;
  var neg_half: fp64 := -0.5;
  assert neg_one == -1.0;
  assert neg_half * -2.0 == 1.0;
  assert -1.5 == -(1.5);
}

method TestApproximateFp64Literals() {
  // Common decimal fractions require ~ prefix
  var tenth: fp64 := ~0.1;
  var fifth: fp64 := ~0.2;
  var three_tenths: fp64 := ~0.3;

  // These are NOT exactly equal due to rounding
  assert tenth + fifth != three_tenths;  // 0.1 + 0.2 != 0.3 in fp64

  // Verify they're in reasonable ranges
  assert ~0.09 < tenth < ~0.11;
  assert ~0.19 < fifth < ~0.21;
  assert ~0.29 < three_tenths < ~0.31;

  // Mathematical constants are approximate
  var pi: fp64 := ~3.14159265358979323846;
  var e: fp64 := ~2.71828182845904523536;

  // Verify constants are in expected ranges
  assert ~3.14 < pi < ~3.15;
  assert ~2.71 < e < ~2.72;

  // Negative approximate values use ~- syntax
  var neg_tenth: fp64 := ~-0.1;
  assert neg_tenth.IsNegative;
  assert -neg_tenth == tenth;  // Negation is exact, so -(-0.1) == 0.1
}

// ===== Syntax Rules Tests =====

method TestApproximateLiteralSyntaxRules() {
  // ~ prefix must encompass the entire literal including sign
  var pos_approx: fp64 := ~0.1;
  var neg_approx: fp64 := ~-0.1;

  // Verify signs are correct
  assert pos_approx.IsPositive;
  assert neg_approx.IsNegative;

  // ~ only applies to literals, not variables or expressions
  var x: fp64 := ~0.1;
  var y: fp64 := x;  // No ~ needed on variable
  var z: fp64 := x + y;  // No ~ needed on expression

  // Verify operations work
  assert z == x + y;
  assert z > x;
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

// ===== Practical Examples =====

method TestFinancialCalculations() {
  // Computing sales tax
  var price: fp64 := ~19.99;
  var taxRate: fp64 := ~0.0825;  // 8.25%
  var tax: fp64 := price * taxRate;
  var total: fp64 := price + tax;

  // Verify calculations
  assert ~1.6 < tax < ~1.7;      // Tax should be approximately $1.65
  assert ~21.6 < total < ~21.7;  // Total should be approximately $21.64
}

method TestScientificComputations() {
  // Circle calculations
  var radius: fp64 := 5.0;  // Exact
  var pi: fp64 := ~3.14159265358979323846;
  var area: fp64 := pi * radius * radius;
  var circumference: fp64 := 2.0 * pi * radius;

  // Verify calculations
  assert 78.5 < area < ~78.6;           // Area of circle with radius 5 ≈ 78.54
  assert ~31.4 < circumference < 31.5;  // Circumference ≈ 31.42
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

// ===== Additional tests =====

method TestLiteralPrecisionBoundaries() {
  // Maximum safely representable integer (2^53)
  var max_safe_int: fp64 := 9007199254740992.0;

  // Verify it's the boundary - beyond this, not all integers are representable
  assert max_safe_int + 1.0 == max_safe_int;  // 2^53 + 1 rounds back to 2^53
  assert max_safe_int + 2.0 == 9007199254740994.0;  // 2^53 + 2 is representable
  assert max_safe_int - 1.0 == 9007199254740991.0;  // Previous int is exactly representable

  // Exact power of 2 fractions
  var tiny_exact: fp64 := 0.00006103515625;  // 2^-14
  assert tiny_exact.IsPositive;
  assert tiny_exact * 16384.0 == 1.0;  // 2^14 * 2^-14 = 1
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

method TestExtremeValues() {
  // Large exact values (powers of 2)
  var large_pow2: fp64 := 1.125899906842624e15;   // 2^50
  assert large_pow2.IsPositive;
  assert large_pow2.IsFinite;

  // Small exact values (negative powers of 2)
  var small_pow2: fp64 := 0.0009765625;           // 2^-10
  assert small_pow2.IsPositive;
  assert small_pow2 * 1024.0 == 1.0;  // 2^-10 * 2^10 = 1

  // Approximate extreme values
  var huge: fp64 := ~1.0e100;
  var tiny: fp64 := ~1.0e-100;
  assert huge.IsFinite && !huge.IsInfinite;
  assert tiny.IsPositive && tiny.IsFinite;
}

method Main() {
  TestExactFp64Literals();
  TestApproximateFp64Literals();
  TestApproximateLiteralSyntaxRules();
  TestTypeInference();
  TestLiteralPrecisionBoundaries();
  TestLiteralArithmetic();
  TestExtremeValues();
  TestFinancialCalculations();
  TestScientificComputations();
  TestRealVsFp64Arithmetic();
}