// RUN: %testDafnyForEachResolver "%s"
// NONUNIFORM: Only C# for now
// RUN: %run --no-verify "%s" > "%t"
// RUN: %diff "%s.expect_run" "%t"

// Comprehensive test of fp64 equality semantics as specified in the design
// Section 5.3: fp64 has hybrid equality semantics
//
// IMPORTANT: Dafny's == operator is NOT IEEE 754 compliant!
// - IEEE 754: +0.0 == -0.0 is true, NaN == NaN is false
// - Dafny ==: +0.0 == -0.0 is false in ghost, NaN == NaN is true in ghost
// - For IEEE 754 semantics, use fp64.Equal() instead

// Test 1: Compiled context equality requires preconditions
method TestCompiledEqualityPreconditions() {
  var x: fp64 := 1.0;
  var y: fp64 := 2.0;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;

  // Valid comparisons (no NaN involved)
  var eq1 := x == y;
  assert !eq1;
  print "1.0 == 2.0: ", eq1, "\n";

  var eq2 := x == x;
  assert eq2;
  print "1.0 == 1.0: ", eq2, "\n";

  var eq3 := inf == inf;
  assert eq3;
  print "+Inf == +Inf: ", eq3, "\n";

  // CRITICAL: Why signed zero check is needed for Dafny's ==
  var pos_zero: fp64 := 0.0;   // Bit pattern: 0x0000000000000000
  var neg_zero: fp64 := -0.0;  // Bit pattern: 0x8000000000000000 (sign bit set!)

  // Dafny's == is BITWISE EQUALITY, not mathematical equality!
  // Since +0 and -0 have different bit patterns, they cannot be compared with ==
  // var eq4 := pos_zero == neg_zero;  // ERROR: Precondition violation!
  //
  // This is fundamentally different from IEEE 754, which treats +0 and -0 as equal

  // For IEEE 754 semantics (mathematical equality), use fp64.Equal:
  var eq4 := fp64.Equal(pos_zero, neg_zero);
  assert eq4;  // IEEE 754: +0 == -0 is true (same mathematical value)
  print "+0.0 == -0.0 (IEEE 754 via fp64.Equal): ", eq4, "\n";

  // Dafny's == works fine when zeros have matching signs (same bit pattern):
  var pos_zero2: fp64 := 0.0;  // Also 0x0000000000000000
  var eq5 := pos_zero == pos_zero2;
  assert eq5;  // Same bit pattern, so == is allowed and returns true
  print "+0.0 == +0.0 (Dafny's == with same bit pattern): ", eq5, "\n";
}

// Test 2: fp64.Equal static method (no preconditions required)
method TestStaticEqualMethod() {
  var x: fp64 := 1.0;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;
  var ninf := fp64.NegativeInfinity;

  // Basic equality
  var eq1 := fp64.Equal(x, x);
  assert eq1;
  print "fp64.Equal(1.0, 1.0): ", eq1, "\n";

  // NaN comparisons (IEEE 754 semantics)
  var eq2 := fp64.Equal(nan, nan);
  assert !eq2;  // NaN != NaN
  print "fp64.Equal(NaN, NaN): ", eq2, "\n";

  var eq3 := fp64.Equal(x, nan);
  assert !eq3;
  print "fp64.Equal(1.0, NaN): ", eq3, "\n";

  // Infinity comparisons
  var eq4 := fp64.Equal(inf, inf);
  assert eq4;
  print "fp64.Equal(+Inf, +Inf): ", eq4, "\n";

  var eq5 := fp64.Equal(inf, ninf);
  assert !eq5;
  print "fp64.Equal(+Inf, -Inf): ", eq5, "\n";

  // Zero comparisons
  var eq6 := fp64.Equal(0.0, -0.0);
  assert eq6;  // IEEE 754: +0 == -0
  print "fp64.Equal(+0.0, -0.0): ", eq6, "\n";
}

// Test 3: Signed Zero Precondition Pattern
method CheckEqualityWithDafny(a: fp64, b: fp64) returns (canUseEqEq: bool, result: bool)
{
  // First check for NaN
  if a.IsNaN || b.IsNaN {
    canUseEqEq := false;
    result := false;  // Dafny's == would be forbidden
    return;
  }

  // Then check for different-signed zeros
  if a.IsZero && b.IsZero && a.IsNegative != b.IsNegative {
    canUseEqEq := false;
    // Can't use Dafny's == (bitwise comparison) but they ARE equal per IEEE 754
    result := false;  // We return false because we can't use ==
    return;
  }

  // Now safe to use ==
  canUseEqEq := true;
  result := a == b;
}

method TestSignedZeroPreconditionPattern() {
  print "=== Demonstrating the Signed Zero Precondition Pattern ===\n";

  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  var regular_value: fp64 := 1.0;

  // Pattern 1: Check if values can be compared with Dafny's ==
  var can1, eq1 := CheckEqualityWithDafny(pos_zero, neg_zero);
  print "Can use == for +0 and -0? ", can1, "\n";  // false - different bit patterns!
  print "  Note: They ARE equal per IEEE 754: ", fp64.Equal(pos_zero, neg_zero), "\n";

  var can2, eq2 := CheckEqualityWithDafny(pos_zero, pos_zero);
  print "Can use == for +0 and +0? ", can2, ", Result: ", eq2, "\n";  // true, true

  var can3, eq3 := CheckEqualityWithDafny(regular_value, regular_value);
  print "Can use == for 1.0 and 1.0? ", can3, ", Result: ", eq3, "\n";  // true, true

  // Pattern 2: When you need IEEE 754 semantics, always use fp64.Equal
  print "\nFor IEEE 754 semantics, always use fp64.Equal:\n";
  print "fp64.Equal(+0, -0) = ", fp64.Equal(pos_zero, neg_zero), " (different bits, same value)\n";
  print "fp64.Equal(+0, +0) = ", fp64.Equal(pos_zero, pos_zero), " (same bits, same value)\n";
}

// Test 4: Dafny == vs IEEE 754 Comparison Table
method TestDafnyVsIEEE754() {
  print "=== Dafny's == vs IEEE 754 (fp64.Equal) ===\n";

  var nan := fp64.NaN;
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  var one: fp64 := 1.0;
  var pos_inf := fp64.PositiveInfinity;

  print "Comparison               | IEEE 754 (fp64.Equal) | Dafny == (compiled) | Dafny == (ghost)\n";
  print "-------------------------|-----------------------|---------------------|------------------\n";

  // NaN comparisons
  print "NaN == NaN               | ";
  print fp64.Equal(nan, nan), "               | ";
  print "FORBIDDEN            | ";
  print "true (reflexive)\n";

  print "1.0 == NaN               | ";
  print fp64.Equal(one, nan), "               | ";
  print "FORBIDDEN            | ";
  print "false\n";

  // Zero comparisons
  print "+0.0 == -0.0             | ";
  print fp64.Equal(pos_zero, neg_zero), "                | ";
  print "FORBIDDEN            | ";
  print "false (bitwise)\n";

  print "+0.0 == +0.0             | ";
  print fp64.Equal(pos_zero, pos_zero), "                | ";
  print (pos_zero == pos_zero), "                | ";
  print "true\n";

  // Regular comparisons
  print "1.0 == 1.0               | ";
  print fp64.Equal(one, one), "                | ";
  print (one == one), "                | ";
  print "true\n";

  print "+Inf == +Inf             | ";
  print fp64.Equal(pos_inf, pos_inf), "                | ";
  print (pos_inf == pos_inf), "                | ";
  print "true\n";

  print "\nKEY INSIGHTS:\n";
  print "- Dafny's == is bitwise equality, NOT IEEE 754 equality!\n";
  print "- In ghost context, == is reflexive (even for NaN) but still bitwise for different values\n";
}

// Test 5: Ghost context reflexive equality (NaN is reflexive in ghost!)
ghost method TestGhostReflexiveEquality() {
  var x: fp64 := 1.0;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;

  // Reflexive property holds for all values in ghost context
  assert x == x;
  assert nan == nan;  // Reflexive even for NaN in ghost!
  assert inf == inf;

  // But non-reflexive comparisons still use bitwise equality (not IEEE 754)
  var y: fp64 := 2.0;
  assert !(x == y);  // Different values

  // Test with variables
  ghost var g1 := nan;
  ghost var g2 := nan;
  assert g1 == g1;  // Reflexive

  // In ghost context, we can still use fp64.Equal for IEEE semantics
  assert !fp64.Equal(nan, nan);  // IEEE 754 semantics
  assert fp64.Equal(x, x);
}

// Test 6: Equality in specifications
method TestEqualityInSpecifications(x: fp64, y: fp64)
  requires !x.IsNaN && !y.IsNaN  // NaN check
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)  // Signed zero check
  ensures x == y ==> x + 1.0 == y + 1.0  // Can use == with full preconditions
{
  if x == y {
    assert x + 1.0 == y + 1.0;
  }
}

// Test 7: Ghost functions and predicates
ghost predicate ReflexiveEqual(x: fp64) {
  x == x  // Always true in ghost context, even for NaN
}

ghost function TestGhostFunction(x: fp64): bool {
  x == x  // Reflexive in ghost context
}

// Test 8: Lemmas with fp64 equality
lemma ReflexivityLemma(x: fp64)
  ensures x == x  // Holds in ghost context
{
  // Trivially true due to reflexivity in ghost context
}

// Test 9: Disequality operators
method TestDisequality() {
  var x: fp64 := 1.0;
  var y: fp64 := 2.0;
  var nan := fp64.NaN;

  // != also requires preconditions in compiled contexts
  var neq1 := x != y;
  assert neq1;
  print "1.0 != 2.0: ", neq1, "\n";

  // Use negation of fp64.Equal for NaN comparisons
  var neq2 := !fp64.Equal(x, nan);
  assert neq2;
  print "!fp64.Equal(1.0, NaN): ", neq2, "\n";
}

// Test 10: Method contracts with fp64 parameters
method ProcessPair(a: fp64, b: fp64) returns (equal: bool)
  requires !a.IsNaN && !b.IsNaN  // NaN check
  requires !(a.IsZero && b.IsZero && a.IsNegative != b.IsNegative)  // Signed zero check
  ensures equal <==> a == b
{
  equal := a == b;  // OK with full preconditions
}

// Test 11: Simple equality in conditional
method TestConditionalEquality() {
  var x: fp64 := 5.0;
  var target: fp64 := 5.0;

  // Full preconditions for ==
  if x == target {
    print "x equals target: true\n";
  }
}

// Test 12: Signed zeros from arithmetic operations
method TestArithmeticSignedZeros() {
  // Arithmetic that produces positive zero
  // Note: Explicit fp64 type needed for new resolver type inference
  var pos_zero_computed: fp64 := 1.0 - 1.0;

  // Arithmetic that produces negative zero
  var neg_zero_computed: fp64 := -0.0 * 1.0;  // Preserves sign of zero

  print "Computed +0: IsNegative = ", pos_zero_computed.IsNegative, "\n";
  print "Computed -0: IsNegative = ", neg_zero_computed.IsNegative, "\n";

  // These have different bit patterns, so can't use ==
  print "Can compare with ==? No (different signed zeros)\n";

  // But they are equal per IEEE 754
  var ieee_equal := fp64.Equal(pos_zero_computed, neg_zero_computed);
  assert ieee_equal;
  print "IEEE 754 equal: ", ieee_equal, "\n";
}

// Test 13: Preconditions must be maintained through derived values
method TestDerivedValuePreconditions() {
  var x: fp64 := 1.0;
  var y: fp64 := 1.0;

  // x and y satisfy preconditions for ==
  var eq1 := x == y;
  assert eq1;
  print "Direct comparison: x == y is ", eq1, "\n";

  // But (x - y) might produce signed zero!
  var diff := x - y;  // This is +0.0
  var neg_diff := -(x - y);  // This produces -0.0 (negation flips sign bit)

  print "diff IsZero: ", diff.IsZero, ", IsNegative: ", diff.IsNegative, "\n";
  print "neg_diff IsZero: ", neg_diff.IsZero, ", IsNegative: ", neg_diff.IsNegative, "\n";

  // These are both zero but with different signs - can't use == without precondition check!
  // var bad := diff == neg_diff;  // ERROR: Would violate precondition (different signed zeros)

  // Check if the precondition for == is satisfied
  var no_nan := !diff.IsNaN && !neg_diff.IsNaN;
  var no_diff_signed_zeros := !(diff.IsZero && neg_diff.IsZero && diff.IsNegative != neg_diff.IsNegative);

  if no_nan && no_diff_signed_zeros {
    print "Precondition for == is satisfied? Yes (but shouldn't be!)\n";
  } else {
    print "Precondition for == is satisfied? No - different signed zeros detected\n";
  }

  // Or just use fp64.Equal for safety (handles all special cases)
  var safe := fp64.Equal(diff, neg_diff);
  print "fp64.Equal(diff, neg_diff): ", safe, " (IEEE 754: +0 == -0)\n";
}

method Main() {
  print "=== Test 1: Compiled Equality Preconditions ===\n";
  TestCompiledEqualityPreconditions();

  print "\n=== Test 2: Static Equal Method ===\n";
  TestStaticEqualMethod();

  print "\n=== Test 3: Signed Zero Precondition Pattern ===\n";
  TestSignedZeroPreconditionPattern();

  print "\n=== Test 4: Dafny == vs IEEE 754 Comparison ===\n";
  TestDafnyVsIEEE754();

  // Tests 5-8 are ghost/compile-time only tests with no runtime output

  print "\n=== Test 9: Disequality ===\n";
  TestDisequality();

  print "\n=== Test 10: Conditional Equality ===\n";
  TestConditionalEquality();

  print "\n=== Test 11: Arithmetic Signed Zeros ===\n";
  TestArithmeticSignedZeros();

  print "\n=== Test 12: Derived Value Preconditions ===\n";
  TestDerivedValuePreconditions();

  print "\nAll tests passed!\n";
}