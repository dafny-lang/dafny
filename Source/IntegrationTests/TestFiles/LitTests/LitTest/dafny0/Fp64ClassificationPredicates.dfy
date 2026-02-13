// RUN: %testDafnyForEachResolver "%s"

// Comprehensive test for fp64 classification predicates
// Tests all IEEE 754 classification predicates as instance members

method BasicClassificationTests() {
  var x: fp64 := ~3.14;
  var zero: fp64 := 0.0;
  var negZero: fp64 := -0.0;
  var large: fp64 := ~1.23e100;
  var small: fp64 := ~4.56e-100;

  assert !x.IsNaN;
  assert x.IsFinite;
  assert !x.IsInfinite;
  assert x.IsNormal;
  assert !x.IsSubnormal;
  assert !x.IsZero;
  assert !x.IsNegative;
  assert x.IsPositive;

  // Test on zero values
  assert zero.IsZero;
  assert zero.IsFinite;
  assert !zero.IsNormal;
  assert zero.IsPositive;
  assert !zero.IsNegative;

  assert negZero.IsZero;
  assert negZero.IsNegative;
  assert !negZero.IsPositive;

  // Test on large values
  assert large.IsNormal;
  assert large.IsFinite;
  assert large.IsPositive;

  // Test on small values
  assert small.IsNormal;  // This value is still in normal range
  assert !small.IsSubnormal;
  assert small.IsFinite;
}

method NegativeValueTests() {
  var negValue: fp64 := -2.5;
  var negLarge: fp64 := ~-1.0e50;
  var negSmall: fp64 := ~-1.0e-50;

  // Test negative value classifications
  assert negValue.IsNegative;
  assert !negValue.IsPositive;
  assert negValue.IsFinite;
  assert negValue.IsNormal;

  assert negLarge.IsNegative;
  assert negLarge.IsNormal;

  assert negSmall.IsNegative;
  assert negSmall.IsNormal;
}

method ChainedPredicateTests() {
  var x: fp64 := 42.0;

  // Test that predicates can be used in expressions
  assert x.IsFinite && x.IsPositive;
  assert x.IsNormal || x.IsSubnormal;  // At least one must be true for finite non-zero
  assert !x.IsNaN;
  assert !x.IsInfinite;

  // Test in conditional expressions
  var classification := if x.IsNaN then "NaN"
                       else if x.IsInfinite then "Infinite"
                       else if x.IsZero then "Zero"
                       else if x.IsNormal then "Normal"
                       else if x.IsSubnormal then "Subnormal"
                       else "Unknown";

  assert classification == "Normal";  // 42.0 is a normal number
}

method PredicateInAssertions() {
  var x: fp64 := 1.5;

  // Test predicates in assertions (ghost context)
  assert x.IsFinite || x.IsInfinite || x.IsNaN;  // Exhaustive for all fp64 values
  // WARNING: The following is FALSE for NaN! NaN is neither positive, negative, nor zero
  // This only passes because x=1.5 here. For general fp64, this would fail.
  assert x.IsPositive || x.IsNegative || x.IsZero;  // Only true for non-NaN values
  assert !(x.IsNormal && x.IsSubnormal);  // Should never both be true
  assert !(x.IsPositive && x.IsNegative);  // Should never both be true
}

method PredicateWithVariables() {
  var values := new fp64[5];
  values[0] := 1.0;
  values[1] := 0.0;
  values[2] := -1.0;
  values[3] := ~1.0e-100;
  values[4] := ~1.0e100;

  var i := 0;
  while i < values.Length
    invariant 0 <= i <= values.Length
  {
    var val := values[i];
    // Test predicates work in loop context
    assert val.IsFinite || val.IsInfinite || val.IsNaN;
    assert !(val.IsNormal && val.IsSubnormal);  // Mutually exclusive

    i := i + 1;
  }
}

method PredicateTypeInference() {
  var x: fp64 := 2.5;

  // Test that predicate results are properly typed as bool
  assert !x.IsNaN;
  assert x.IsFinite;
  assert !x.IsInfinite;
  assert x.IsNormal;
  assert !x.IsSubnormal;
  assert !x.IsZero;
  assert !x.IsNegative;
  assert x.IsPositive;

  // Test in boolean operations
  var combined := x.IsNaN || x.IsFinite || x.IsInfinite;
  assert combined;  // At least one must be true

  var allFalse := !x.IsNaN && !x.IsFinite && !x.IsInfinite;
  assert !allFalse;  // Can't all be false
}

method MethodParameterPredicates(value: fp64) returns (isSpecial: bool)
  ensures isSpecial == (value.IsNaN || value.IsInfinite || value.IsZero)
{
  // Test predicates on method parameters
  isSpecial := value.IsNaN || value.IsInfinite || value.IsZero;
}

method TestMethodParameterPredicates() {
  // Test with normal value
  var normal := MethodParameterPredicates(42.0);
  assert !normal;

  // Test with special values
  var nan := MethodParameterPredicates(fp64.NaN);
  var inf := MethodParameterPredicates(fp64.PositiveInfinity);
  var zero := MethodParameterPredicates(0.0);
  assert nan && inf && zero;

  // Test with edge cases
  var subnormal := MethodParameterPredicates(~4.9406564584124654e-324);
  var negInf := MethodParameterPredicates(fp64.NegativeInfinity);
  var negZero := MethodParameterPredicates(-0.0);
  assert !subnormal && negInf && negZero;
}

// Ghost method to test predicates in ghost context
ghost method GhostPredicateTests() {
  var x: fp64 := ~3.14;

  // All predicates should work in ghost context
  ghost var isNaN := x.IsNaN;
  ghost var isFinite := x.IsFinite;
  ghost var isInfinite := x.IsInfinite;
  ghost var isNormal := x.IsNormal;
  ghost var isSubnormal := x.IsSubnormal;
  ghost var isZero := x.IsZero;
  ghost var isNegative := x.IsNegative;
  ghost var isPositive := x.IsPositive;

  // Ghost assertions
  assert x.IsFinite || x.IsInfinite || x.IsNaN;  // Exhaustive for all fp64
  assert x.IsPositive || x.IsNegative || x.IsZero;  // Only true because x=~3.14; would fail for NaN
}

method ComprehensivePredicateTest() {
  // Test all predicates on various values
  var testValues := new fp64[6];
  testValues[0] := 0.0;      // Zero
  testValues[1] := -0.0;     // Negative zero
  testValues[2] := 1.0;      // Normal positive
  testValues[3] := -1.0;     // Normal negative
  testValues[4] := ~1.0e-200; // Normal value (subnormal boundary is ~2.225e-308)
  testValues[5] := ~1.0e200;  // Large normal

  var i := 0;
  while i < testValues.Length
    invariant 0 <= i <= testValues.Length
  {
    var val := testValues[i];

    // Verify classification completeness and mutual exclusivity
    assert val.IsNaN || val.IsFinite || val.IsInfinite;  // Exactly one must be true
    if val.IsFinite && !val.IsZero {
      assert val.IsNormal || val.IsSubnormal;  // Finite non-zero must be one of these
    }

    // Verify mutual exclusivity where appropriate
    assert !(val.IsNormal && val.IsSubnormal);
    assert !(val.IsPositive && val.IsNegative);
    assert !(val.IsFinite && val.IsInfinite);

    i := i + 1;
  }
}

method TestSpecialValues() {
  // Test NaN
  var nan := fp64.NaN;
  assert nan.IsNaN;
  assert !nan.IsFinite;
  assert !nan.IsInfinite;
  assert !nan.IsNormal;
  assert !nan.IsSubnormal;
  assert !nan.IsZero;
  assert !nan.IsNegative;
  assert !nan.IsPositive;

  // Test Positive Infinity
  var posInf := fp64.PositiveInfinity;
  assert !posInf.IsNaN;
  assert !posInf.IsFinite;
  assert posInf.IsInfinite;
  assert !posInf.IsNormal;
  assert !posInf.IsSubnormal;
  assert !posInf.IsZero;
  assert !posInf.IsNegative;
  assert posInf.IsPositive;

  // Test Negative Infinity
  var negInf := fp64.NegativeInfinity;
  assert !negInf.IsNaN;
  assert !negInf.IsFinite;
  assert negInf.IsInfinite;
  assert !negInf.IsNormal;
  assert !negInf.IsSubnormal;
  assert !negInf.IsZero;
  assert negInf.IsNegative;
  assert !negInf.IsPositive;

  // Test actual subnormal value (smallest positive subnormal = 2^-1074)
  var subnormal: fp64 := ~4.9406564584124654e-324; // This is approximately 2^(-1074)
  assert !subnormal.IsNaN;
  assert subnormal.IsFinite;
  assert !subnormal.IsInfinite;
  assert !subnormal.IsNormal;
  assert subnormal.IsSubnormal;
  assert !subnormal.IsZero;
  assert !subnormal.IsNegative;
  assert subnormal.IsPositive;

  // Test negative subnormal value
  var negSubnormal: fp64 := ~-4.9406564584124654e-324; // This is approximately -2^(-1074)
  assert !negSubnormal.IsNaN;
  assert negSubnormal.IsFinite;
  assert !negSubnormal.IsInfinite;
  assert !negSubnormal.IsNormal;
  assert negSubnormal.IsSubnormal;
  assert !negSubnormal.IsZero;
  assert negSubnormal.IsNegative;
  assert !negSubnormal.IsPositive;
}

method TestPredicatesWithStaticMethods() {
  // Test that static methods work alongside instance predicates
  var x: fp64 := ~3.14;

  // Test instance predicates work correctly
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

  // Verify static Equal method works with values tested by predicates
  assert fp64.Equal(x, x);  // Self-equality (except for NaN)
  assert !fp64.Equal(x, nan);  // Normal number != NaN

  // Verify arithmetic operations produce expected results based on predicates
  assert x + 1.0 > x;  // Adding positive increases value
  assert x - 1.0 < x;  // Subtracting positive decreases value
  assert x * 2.0 > x;  // Multiplying by >1 increases positive value
  assert x / 2.0 < x;  // Dividing by >1 decreases positive value
  assert (-x).IsNegative;  // Negation of positive is negative

  // Verify comparison operations work with predicate-tested values
  assert x < 5.0;   // ~3.14 < 5.0
  assert x <= 5.0;  // ~3.14 <= 5.0
  assert x > 1.0;   // ~3.14 > 1.0
  assert x >= 1.0;  // ~3.14 >= 1.0

  // Test predicates with special constants
  var posInf := fp64.PositiveInfinity;
  assert posInf.IsInfinite && posInf.IsPositive;
  assert fp64.Equal(posInf, posInf);

  var absResult := fp64.Abs(-4.0);
  assert absResult == 4.0;
  assert absResult.IsFinite && absResult.IsPositive;
}

method TestBoundaryValues() {
  // Test maximum and minimum values
  var maxVal := fp64.MaxValue;
  assert maxVal.IsFinite;
  assert maxVal.IsNormal;
  assert maxVal.IsPositive;
  assert !maxVal.IsNegative;

  var minVal := fp64.MinValue;  // Most negative finite value
  assert minVal.IsFinite;
  assert minVal.IsNormal;
  assert minVal.IsNegative;
  assert !minVal.IsPositive;

  // Test machine epsilon (smallest value that changes 1.0 when added)
  var epsilon := fp64.Epsilon;
  assert epsilon.IsFinite;
  assert epsilon.IsNormal;  // Epsilon (2^-52) is in the normal range
  assert epsilon.IsPositive;
  assert !epsilon.IsNegative;

  // Test value near normal/subnormal boundary
  var nearBoundary: fp64 := ~2.225e-308;  // Close to smallest normal
  assert nearBoundary.IsFinite;
  // Can't assert IsNormal vs IsSubnormal without knowing exact value after rounding

  // Test largest subnormal (just below smallest normal)
  var largestSubnormal: fp64 := ~2.225073858507201e-308;  // Just below 2^-1022
  assert largestSubnormal.IsFinite;
  // Exact classification depends on rounding
}

method TestMutualExclusivity() {
  // Systematically test that classifications are mutually exclusive
  var testVals := [fp64.NaN, fp64.PositiveInfinity, 0.0, 1.0, ~4.94e-324];

  var i := 0;
  while i < |testVals|
    invariant 0 <= i <= |testVals|
  {
    var v := testVals[i];

    // NaN, Finite, and Infinite are mutually exclusive
    var count1 := (if v.IsNaN then 1 else 0) +
                  (if v.IsFinite then 1 else 0) +
                  (if v.IsInfinite then 1 else 0);
    assert count1 == 1;  // Exactly one must be true

    // For finite values, Normal, Subnormal, and Zero are mutually exclusive
    if v.IsFinite {
      var count2 := (if v.IsNormal then 1 else 0) +
                    (if v.IsSubnormal then 1 else 0) +
                    (if v.IsZero then 1 else 0);
      assert count2 == 1;  // Exactly one must be true
    }

    i := i + 1;
  }
}

method Main() {
  BasicClassificationTests();
  NegativeValueTests();
  ChainedPredicateTests();
  PredicateInAssertions();
  PredicateWithVariables();
  PredicateTypeInference();
  TestMethodParameterPredicates();
  ComprehensivePredicateTest();
  TestSpecialValues();
  TestPredicatesWithStaticMethods();
  TestBoundaryValues();
  TestMutualExclusivity();
}
