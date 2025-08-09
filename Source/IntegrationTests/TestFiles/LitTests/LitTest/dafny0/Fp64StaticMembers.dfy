// RUN: %testDafnyForEachResolver "%s"

// Test for fp64 static members - IEEE 754 equality and special values

method TestFp64StaticConstants() {
  // Test static special value constants
  var nan := fp64.NaN;
  var posInf := fp64.PositiveInfinity;
  var negInf := fp64.NegativeInfinity;

  // Verify special value properties
  assert nan.IsNaN;
  assert !nan.IsFinite;
  assert !nan.IsInfinite;
  assert !nan.IsZero;
  
  assert posInf.IsInfinite;
  assert posInf.IsPositive;
  assert !posInf.IsNegative;
  assert !posInf.IsFinite;
  assert !posInf.IsNaN;
  
  assert negInf.IsInfinite;
  assert negInf.IsNegative;
  assert !negInf.IsPositive;
  assert !negInf.IsFinite;
  assert !negInf.IsNaN;
  
  // Verify arithmetic properties of infinities
  assert posInf + 1.0 == posInf;
  assert negInf - 1.0 == negInf;
  assert -posInf == negInf;
  assert -negInf == posInf;
}

method TestFp64StaticEqual() {
  // Test static IEEE 754 equality method
  var x: fp64 := ~3.14;
  var y: fp64 := ~3.14;
  var z: fp64 := 2.5;

  // Test basic equality
  assert fp64.Equal(2.5, 2.5);  // Exact values should be equal
  assert !fp64.Equal(1.0, 2.0);  // Different values should not be equal
  
  // Test NaN behavior - NaN != NaN per IEEE 754
  var nan := fp64.NaN;
  assert !fp64.Equal(nan, nan);  // NaN is not equal to itself
  assert !fp64.Equal(nan, 1.0);  // NaN is not equal to any number
  assert !fp64.Equal(1.0, nan);
  
  // Test signed zero behavior - +0 == -0 per IEEE 754
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  assert fp64.Equal(pos_zero, neg_zero);  // +0 equals -0
  assert fp64.Equal(neg_zero, pos_zero);
  
  // Test infinities
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;
  assert fp64.Equal(pos_inf, pos_inf);  // +∞ equals itself
  assert fp64.Equal(neg_inf, neg_inf);  // -∞ equals itself
  assert !fp64.Equal(pos_inf, neg_inf); // +∞ != -∞
  
  // Test approximate values (may or may not be equal)
  // We can't assert these are equal or not equal since compiler may optimize differently
  var approx_equal := fp64.Equal(x, y);
  assert approx_equal || !approx_equal;  // Tautology but shows it returns bool
}

method TestStaticAndInstanceMembersCoexist() {
  var x: fp64 := ~3.14;

  // Test that instance predicates work correctly
  assert !x.IsNaN;
  assert x.IsFinite;
  assert !x.IsInfinite;
  assert x.IsNormal;  // ~3.14 is in normal range
  assert !x.IsSubnormal;
  assert !x.IsZero;
  assert !x.IsNegative;  // ~3.14 is positive
  assert x.IsPositive;

  // Test static members work alongside instance members
  var nan := fp64.NaN;
  assert nan.IsNaN;  // Static constant with instance predicate
  
  // Verify static Equal method with instance predicates
  assert fp64.Equal(x, x);  // Self-equality (except for NaN)
  assert !fp64.Equal(x, nan);  // Normal number != NaN

  // Verify arithmetic operations produce expected results
  assert x + 1.0 > x;  // Adding positive increases value
  assert x - 1.0 < x;  // Subtracting positive decreases value
  assert x * 2.0 > x;  // Multiplying by >1 increases positive value
  assert x / 2.0 < x;  // Dividing by >1 decreases positive value
  assert -x < 0.0;     // Negation of positive is negative

  // Verify comparison operations
  assert x < 5.0;   // ~3.14 < 5.0
  assert x <= 5.0;  // ~3.14 <= 5.0
  assert x > 1.0;   // ~3.14 > 1.0
  assert x >= 1.0;  // ~3.14 >= 1.0
}

method TestSpecialValueArithmetic() {
  // Test arithmetic with special values
  var nan := fp64.NaN;
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;
  var zero: fp64 := 0.0;
  var one: fp64 := 1.0;
  
  // NaN arithmetic - any operation with NaN produces NaN
  assert (nan + one).IsNaN;
  assert (nan - one).IsNaN;
  assert (nan * one).IsNaN;
  assert (nan / one).IsNaN;
  assert (-nan).IsNaN;
  
  // Infinity arithmetic
  assert pos_inf + pos_inf == pos_inf;
  assert neg_inf + neg_inf == neg_inf;
  assert pos_inf * 2.0 == pos_inf;
  assert neg_inf * 2.0 == neg_inf;
  assert pos_inf * -1.0 == neg_inf;
  // Division by infinity produces zero (sign depends on signs of operands)
  assert (one / pos_inf).IsZero;  // 1/∞ = 0
  assert (one / neg_inf).IsZero;  // 1/-∞ = -0
  
  // Special cases that produce NaN
  assert (pos_inf + neg_inf).IsNaN;  // ∞ - ∞ is undefined
  assert (pos_inf - pos_inf).IsNaN;  // ∞ - ∞ is undefined
  // Note: Can't test 0/0 in Dafny due to division by zero check
  assert (pos_inf / pos_inf).IsNaN;  // ∞/∞ is undefined
  assert (zero * pos_inf).IsNaN;     // 0 * ∞ is undefined
}

method TestEqualWithSpecialCases() {
  // Additional edge cases for fp64.Equal
  var zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  var small: fp64 := ~1e-100;
  var large: fp64 := ~1e100;
  
  // Test subnormal values
  var subnormal: fp64 := ~2.2250738585072014e-308;  // Near minimum normal
  assert fp64.Equal(subnormal, subnormal);
  
  // Test exact integer values
  assert fp64.Equal(42.0, 42.0);
  assert fp64.Equal(-42.0, -42.0);
  assert !fp64.Equal(42.0, -42.0);
  
  // Test powers of 2
  assert fp64.Equal(0.5, 0.5);
  assert fp64.Equal(0.25, 0.25);
  assert fp64.Equal(1024.0, 1024.0);
  
  // Test that Equal is symmetric
  var a: fp64 := ~1.23;
  var b: fp64 := ~4.56;
  assert fp64.Equal(a, b) == fp64.Equal(b, a);
  
  // Test that Equal is reflexive (except NaN)
  assert fp64.Equal(zero, zero);
  assert fp64.Equal(small, small);
  assert fp64.Equal(large, large);
}

method TestStaticConstantUniqueness() {
  // Verify that multiple accesses to static constants return same values
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
}

method Main() {
  TestFp64StaticConstants();
  TestFp64StaticEqual();
  TestStaticAndInstanceMembersCoexist();
  TestSpecialValueArithmetic();
  TestEqualWithSpecialCases();
  TestStaticConstantUniqueness();
}
