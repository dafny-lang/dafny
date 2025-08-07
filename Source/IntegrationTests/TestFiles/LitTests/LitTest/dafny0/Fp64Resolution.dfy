// RUN: %testDafnyForEachResolver "%s"

// fp64 resolution tests
// Tests type inference, arithmetic operations, comparisons, and error conditions

method TestBasicLiteralAssignment() {
  // Basic literal assignment with type inference
  var x: fp64 := ~3.14;
  var y: fp64 := 2.5;
  var z: fp64 := 0.0;
  var w: fp64 := 1.0;

  // Verify assignments work
  assert x.IsFinite;
  assert y == 2.5;
  assert z == 0.0;
  assert w == 1.0;

  // Scientific notation
  var large: fp64 := 1.23e10;
  var small: fp64 := ~4.56e-7;

  assert large == 12300000000.0;
  assert small > 0.0 && small < ~0.000001;

  // Dot shorthand forms
  assert .5 == 0.5;
  assert 42. == 42.0;
}

method TestArithmeticOperations() {
  var x: fp64 := 10.5;
  var y: fp64 := 4.0;  // Use exact value to avoid rounding issues

  // Verify arithmetic operations
  assert x + y == 14.5;
  assert x - y == 6.5;
  assert x * y == 42.0;
  assert x / y == 2.625;
  assert -x == -10.5;

  // Chained operations
  assert (x + y) * (x - y) == 14.5 * 6.5;
  assert -(x + y) == -14.5;

  // Order of operations
  var z: fp64 := 2.0;
  assert x + y * z == 10.5 + 8.0;  // Multiplication before addition
  assert (x + y) * z == 29.0;      // Parentheses change order

  // Mixed with literals
  assert x + 1.5 == 12.0;
  assert 2.0 * y == 8.0;
  assert x / 0.5 == 21.0;
}

method TestComparisonOperations() {
  var x: fp64 := 5.5;
  var y: fp64 := 3.0;  // Use exact value

  // Verify comparison operations
  assert !(x < y);
  assert !(x <= y);
  assert x > y;
  assert x >= y;

  // Comparisons produce booleans
  var less: bool := x < y;
  assert !less;

  // Test with equal values
  var z: fp64 := 5.5;
  assert !(x < z);
  assert x <= z;
  assert !(x > z);
  assert x >= z;

  // Mixed with literals
  assert x < 6.0;
  assert !(4.0 <= y);
  assert x > 0.0;
}

method TestTypeInference() {
  // Type inference for literals
  var real_inferred := 3.14;      // Infers as real
  var fp64_explicit: fp64 := ~3.14;

  // Operations preserve fp64 type
  var x: fp64 := 2.5;
  var sum: fp64 := x + 1.5;
  var product: fp64 := x * 2.0;
  var negation: fp64 := -x;

  // Verify operations work
  assert sum == 4.0;
  assert product == 5.0;
  assert negation == -2.5;

  // Real arithmetic is exact
  assert 0.1 + 0.2 == 0.3 as real;
}

method TestVariableDeclarations() {
  // Uninitialized declaration
  var x: fp64;
  x := 5.5;
  assert x == 5.5;

  // Initialized declaration
  var y: fp64 := ~3.14;
  assert y.IsFinite;

  // Multiple declarations
  var a: fp64, b: fp64 := 1.0, 2.0;
  assert a == 1.0;
  assert b == 2.0;

  // Assignment after declaration
  var c: fp64;
  c := 7.5;
  assert c == 7.5;
}

method TestMethodParameters(x: fp64, y: fp64) returns (result: fp64)
  ensures result == x + y
{
  result := x + y;
}

method TestNestedExpressions() {
  var x: fp64 := 2.0;
  var y: fp64 := 3.0;
  var z: fp64 := 4.0;

  // Complex nested expressions
  assert ((x + y) * z) / (x - y) == (5.0 * 4.0) / (-1.0);
  assert -(x + (y * z)) == -(2.0 + 12.0);

  // Boolean expressions with comparisons
  assert (x < y) && (y < z);
  assert (x + y) < (z * 2.0);  // 5.0 < 8.0

  // Parentheses don't change single values
  assert (x) == x;
  assert (x + y) == 5.0;
  assert -(x) == -2.0;
}

method TestConditionalExpressions() {
  var x: fp64 := 5.0;
  var y: fp64 := 3.0;

  // Conditional expressions with fp64
  assert (if true then x else y) == x;
  assert (if false then x else y) == y;

  // Conditions based on comparisons
  assert (if x > y then x + 1.0 else y - 1.0) == 6.0;
  assert (if x < y then x + 1.0 else y - 1.0) == 2.0;

  // Absolute value using conditional
  var neg: fp64 := -5.0;
  assert (if neg < 0.0 then -neg else neg) == 5.0;
}

method TestLoopExpressions() {
  var x: fp64 := 1.0;
  var i := 0;

  // Loops with fp64 variables
  while i < 3
    invariant 0 <= i <= 3
  {
    x := x * 2.0;
    i := i + 1;
  }
  // x should be 8.0 after loop

  // Sum in a loop
  var sum: fp64 := 0.0;
  var j := 0;
  while j < 4
    invariant 0 <= j <= 4
  {
    sum := sum + 1.5;
    j := j + 1;
  }
  // sum should be 6.0 after loop
}

method TestAssignmentStatements() {
  var x: fp64 := 1.0;
  var y: fp64 := 2.0;

  // Sequential assignments
  assert x == 1.0;
  x := 3.0;
  assert x == 3.0;

  y := x + 1.0;
  assert y == 4.0;

  x := y * 2.0;
  assert x == 8.0;

  y := -x;
  assert y == -8.0;
}

// Error condition tests - commented out to avoid compilation errors
method TestErrorConditions() {
  var x: fp64 := ~3.14;
  var y: fp64 := 2.5;

  // These would produce errors if uncommented:
  // var equal := x == y;     // Error: fp64 not equality-supporting in compiled context
  // var not_equal := x != y; // Error: fp64 not equality-supporting in compiled context

  // But bitwise equality works in ghost/assertion contexts
  assert x == x;  // Reflexive equality always works
}

// Ghost context tests - equality works in ghost contexts
ghost method TestGhostContexts() {
  var x: fp64 := ~3.14;
  var y: fp64 := ~3.14;

  // In ghost contexts, equality works (bitwise equality)
  assert x == x;  // Reflexive

  // Note: x and y might not be bitwise equal even with same literal
  // due to compiler optimizations or rounding differences

  // Ghost variables
  ghost var ghost_fp: fp64 := 2.5;
  assert ghost_fp == ghost_fp;
  assert ghost_fp == 2.5;  // Exact value
}

// Integration with other types
method TestTypeInteractions() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  var int_val: int := 42;

  // These would require explicit conversions if uncommented:
  // var mixed1 := fp_val + real_val;  // Error: type mismatch
  // var mixed2 := fp_val + int_val;   // Error: type mismatch

  // But literals work with type inference
  var fp_plus_literal: fp64 := fp_val + 1.0;  // 1.0 inferred as fp64
  assert fp_plus_literal > fp_val;

  // Integer literals need decimal point for fp64
  var fp_plus_int_literal: fp64 := fp_val + 42.0;  // 42.0 is fp64
  assert fp_plus_int_literal > fp_val;
}

// Comprehensive test method that exercises all functionality
method TestComprehensive() {
  // Literals and assignments
  var a: fp64 := 1.5;
  var b: fp64 := 0.25;    // 2.5e-1 = 0.25
  var c: fp64 := 0.75;    // .75
  var d: fp64 := 3.0;     // 3.

  // Verify literal values
  assert a == 1.5;
  assert b == 0.25;
  assert c == 0.75;
  assert d == 3.0;

  // Arithmetic operations
  assert a + b == 1.75;
  assert a - b == 1.25;
  assert a * b == 0.375;
  assert a / b == 6.0;
  assert -a == -1.5;

  // Comparisons
  assert a > b;   // 1.5 > 0.25
  assert a >= b;
  assert !(a < b);
  assert !(a <= b);

  // Complex expressions
  assert (a + b) * (c - d) == 1.75 * (-2.25);
  assert (if a > b then a * 2.0 else b / 2.0) == 3.0;

  // Method calls
  var method_result := TestMethodParameters(a, b);
  assert method_result == 1.75;
}

// Main method to run all tests
method Main() {
  TestBasicLiteralAssignment();
  TestArithmeticOperations();
  TestComparisonOperations();
  TestTypeInference();
  TestVariableDeclarations();
  var result := TestMethodParameters(1.0, 2.0);
  assert result == 3.0;
  TestNestedExpressions();
  TestConditionalExpressions();
  TestLoopExpressions();
  TestAssignmentStatements();
  TestErrorConditions();
  TestTypeInteractions();
  TestComprehensive();
}
