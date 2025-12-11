// RUN: %testDafnyForEachResolver "%s"

// fp32 language integration and resolution tests
// Tests how fp32 integrates with Dafny's language constructs, type inference, and operations

method TestBasicLiteralAssignment() {
  // Basic literal assignment with type inference
  var x: fp32 := ~3.14;
  var y: fp32 := 2.5;
  var z: fp32 := 0.0;
  var w: fp32 := 1.0;

  // Verify assignments work
  assert x.IsFinite;
  assert y == 2.5;
  assert z == 0.0;
  assert w == 1.0;

  // Scientific notation
  var large: fp32 := ~1.23e10;
  var small: fp32 := ~4.56e-7;

  assert large == ~12300000000.0;
  assert 0.0 < small < ~0.000001;

  // Dot shorthand forms with fp32
  var half: fp32 := .5;
  var forty_two: fp32 := 42.;
  assert half == 0.5;
  assert forty_two == 42.0;
}

method TestArithmeticOperations() {
  var x: fp32 := 10.5;
  var y: fp32 := 4.0;  // Use exact value to avoid rounding issues

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
  var z: fp32 := 2.0;
  assert x + y * z == 10.5 + 8.0;  // Multiplication before addition
  assert (x + y) * z == 29.0;      // Parentheses change order

  // Mixed with literals
  assert x + 1.5 == 12.0;
  assert 2.0 * y == 8.0;
  assert x / 0.5 == 21.0;
}

method TestComparisonOperations() {
  var x: fp32 := 5.5;
  var y: fp32 := 3.0;  // Use exact value

  // Verify comparison operations
  assert !(x < y);
  assert !(x <= y);
  assert x > y;
  assert x >= y;

  // Comparisons produce booleans
  var less: bool := x < y;
  assert !less;

  // Test with equal values
  var z: fp32 := 5.5;
  assert !(x < z);
  assert x <= z;
  assert !(x > z);
  assert x >= z;

  // Mixed with literals
  assert x < 6.0;
  assert x <= 6.0;
  assert 4.0 > y;
  assert 4.0 >= y;
  assert x > 0.0;
  assert x >= 0.0;
}

method TestVariableDeclarations() {
  // Uninitialized declaration
  var x: fp32;
  x := 5.5;
  assert x == 5.5;

  // Initialized declaration
  var y: fp32 := ~3.14;
  assert y.IsFinite;

  // Multiple declarations
  var a: fp32, b: fp32 := 1.0, 2.0;
  assert a == 1.0;
  assert b == 2.0;

  // Assignment after declaration
  var c: fp32;
  c := 7.5;
  assert c == 7.5;
}

method TestMethodParameters(x: fp32, y: fp32) returns (result: fp32)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsInfinite && y.IsInfinite && x.IsPositive != y.IsPositive)
  ensures result == x + y
{
  result := x + y;
}

method TestNestedExpressions() {
  var x: fp32 := 2.0;
  var y: fp32 := 3.0;
  var z: fp32 := 4.0;

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
  var x: fp32 := 5.0;
  var y: fp32 := 3.0;

  // Conditional expressions with fp32
  assert (if true then x else y) == x;
  assert (if false then x else y) == y;

  // Conditions based on comparisons
  assert (if x > y then x + 1.0 else y - 1.0) == 6.0;
  assert (if x < y then x + 1.0 else y - 1.0) == 2.0;

  // Absolute value using conditional
  var neg: fp32 := -5.0;
  assert (if neg < 0.0 then -neg else neg) == 5.0;
}

method TestLoopExpressions() {
  var x: fp32 := 1.0;
  var i := 0;

  // Loops with fp32 variables
  while i < 3
    invariant 0 <= i <= 3
    invariant i == 0 ==> x == 1.0
    invariant i == 1 ==> x == 2.0
    invariant i == 2 ==> x == 4.0
    invariant i == 3 ==> x == 8.0
  {
    x := x * 2.0;
    i := i + 1;
  }
  assert x == 8.0;  // Verify loop result

  // Sum in a loop
  var sum: fp32 := 0.0;
  var j := 0;
  while j < 4
    invariant 0 <= j <= 4
    invariant j == 0 ==> sum == 0.0
    invariant j == 1 ==> sum == 1.5
    invariant j == 2 ==> sum == 3.0
    invariant j == 3 ==> sum == 4.5
    invariant j == 4 ==> sum == 6.0
  {
    sum := sum + 1.5;
    j := j + 1;
  }
  assert sum == 6.0;  // Verify loop result
}

method TestAssignmentStatements() {
  var x: fp32 := 1.0;
  var y: fp32 := 2.0;

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

// Integration with other types
method TestTypeInteractions() {
  var fp_val: fp32 := ~3.14;

  // But literals work with type inference
  var fp_plus_literal: fp32 := fp_val + 1.0;  // 1.0 inferred as fp32
  assert fp_plus_literal > fp_val;

  // Integer literals need decimal point for fp32
  var fp_plus_int_literal: fp32 := fp_val + 42.0;  // 42.0 is fp32
  assert fp_plus_int_literal > fp_val;
}

// Main method to run all tests
method Main() {
  TestBasicLiteralAssignment();
  TestArithmeticOperations();
  TestComparisonOperations();
  TestVariableDeclarations();
  var result := TestMethodParameters(1.0, 2.0);
  assert result == 3.0;
  TestNestedExpressions();
  TestConditionalExpressions();
  TestLoopExpressions();
  TestAssignmentStatements();
  TestTypeInteractions();
}
