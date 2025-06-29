// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

// Comprehensive test for scientific notation and trailing dot support

method BasicScientificNotation() {
  // Basic positive exponents
  var a := 1.23e2;     // 123.0
  var b := 1.23E2;     // 123.0 (uppercase E)
  var c := 1.23e+2;    // 123.0 (explicit +)
  
  // Basic negative exponents  
  var d := 1.23e-2;    // 0.0123
  var e := 1.23E-2;    // 0.0123 (uppercase E)
  
  // Zero exponent
  var f := 1.23e0;     // 1.23
  var g := 1.23e+0;    // 1.23
  var h := 1.23e-0;    // 1.23
  
  // Verify basic equivalences
  assert a == b && b == c && c == 123.0;
  assert d == e && e == 0.0123;
  assert f == g && g == h && h == 1.23;
}

method IntegerScientificNotation() {
  // Integer base with scientific notation
  var a := 5e2;        // 500.0
  var b := 5E2;        // 500.0
  var c := 5e+2;       // 500.0
  var d := 5e-1;       // 0.5
  var e := 5e0;        // 5.0
  
  assert a == b && b == c && c == 500.0;
  assert d == 0.5;
  assert e == 5.0;
}

method TrailingDotLiterals() {
  // Basic trailing dot literals
  var a := 1.;         // 1.0
  var b := 123.;       // 123.0
  var c := 0.;         // 0.0
  
  // Trailing dots with underscores
  var d := 1_000.;     // 1000.0
  
  // Verify values
  assert a == 1.0;
  assert b == 123.0;
  assert c == 0.0;
  assert d == 1000.0;
}

method ScientificNotationArithmetic() {
  // Arithmetic with scientific notation
  var a := 1.5e2;      // 150.0
  var b := 3.0e1;      // 30.0
  var c := 2.0e-1;     // 0.2
  
  // Basic operations
  assert a + b == 180.0;
  assert a - b == 120.0;
  assert a * c == 30.0;
  assert a / b == 5.0;
  
  // Mixed with regular literals
  assert a + 50.0 == 200.0;
  assert b * 2.0 == 60.0;
  assert c + 0.8 == 1.0;
}

method EdgeCases() {
  // Zero with exponents
  var a := 0.0e5;      // 0.0
  var b := 0e-3;       // 0.0
  var c := 0.;         // 0.0
  
  assert a == b && b == c && c == 0.0;
  
  // Small values
  var d := 9.99e-1;    // 0.999
  var e := 1.01e0;     // 1.01
  
  assert d < 1.0;
  assert e > 1.0;
}

method UnderscoreSupport() {
  // Test underscores with scientific notation
  var a := 1_2.3_4e1_0;    // 123.4e10
  var b := 5_0.0e-4;       // 50.0e-4 = 0.005
  var c := 1_000.;         // 1000.0
  
  assert a == 123400000000.0;
  assert b == 0.005;
  assert c == 1000.0;
}

method TypeInference() {
  // Test that type inference works correctly
  var small := 1.0e-5;     // 0.00001
  var medium := 1.0e0;     // 1.0
  var large := 1.0e5;      // 100000.0
  
  // These should all be inferred as real type
  assert small < medium && medium < large;
}

method ExpressionContexts() {
  // Test scientific notation in various expression contexts
  assert 1.0e2 == 100.0;
  assert 5.0e-1 == 0.5;
  assert 1.0e0 == 1.0;
  
  // In assertions with trailing dots
  assert 1. == 1.0;
  assert 100. == 100.0;
  
  // Test parenthesized expressions
  assert (1.0e2) == 100.0;
  assert (5.0e0) == 5.0;
  assert (5.) == 5.0;
}
