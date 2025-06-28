// RUN: %exits-with 0 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test basic scientific notation parsing and semantics
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
  assert a == b == c == 123.0;
  assert d == e == 0.0123;
  assert f == g == h == 1.23;
  
  // Cross-format equivalences
  assert a == b == c;
  assert d == e;
  assert f == g == h;
}

method IntegerScientificNotation() {
  // Integer base with scientific notation
  var a := 5e2;        // 500.0
  var b := 5E2;        // 500.0
  var c := 5e+2;       // 500.0
  var d := 5e-1;       // 0.5
  var e := 5e0;        // 5.0
  
  assert a == b == c == 500.0;
  assert d == 0.5;
  assert e == 5.0;
  
  assert a == b == c;
}

method TrailingDotLiterals() {
  // Basic trailing dot literals
  var a := 1.;         // 1.0
  var b := 123.;       // 123.0
  var c := 0.;         // 0.0
  
  // Trailing dots with scientific notation
  var d := 5.e2;       // 500.0
  var e := 42.E-1;     // 4.2
  var f := 1.e0;       // 1.0
  
  // Trailing dots with underscores
  var g := 1_000.;     // 1000.0
  var h := 1_2.e3;     // 12000.0
  
  // Verify values
  assert a == 1.0;
  assert b == 123.0;
  assert c == 0.0;
  assert d == 500.0;
  assert e == 4.2;
  assert f == 1.0;
  assert g == 1000.0;
  assert h == 12000.0;
  
  // Equivalences with traditional forms
  assert a == 1.0;
  assert b == 123.0;
  assert d == 5.0e2;
  assert e == 42.0E-1;
}

method LeadingDotLiterals() {
  // Basic leading dot literals
  var a := .1;         // 0.1
  var b := .25;        // 0.25
  var c := .0;         // 0.0
  
  // Leading dots with scientific notation
  var d := .5e3;       // 500.0
  var e := .75E-2;     // 0.0075
  var f := .1e0;       // 0.1
  
  // Leading dots with underscores
  var g := .1_2_3;     // 0.123
  var h := .5_0e2;     // 50.0
  
  // Verify values
  assert a == 0.1;
  assert b == 0.25;
  assert c == 0.0;
  assert d == 500.0;
  assert e == 0.0075;
  assert f == 0.1;
  assert g == 0.123;
  assert h == 50.0;
  
  // Equivalences with traditional forms
  assert a == 0.1;
  assert b == 0.25;
  assert d == 0.5e3;
  assert e == 0.75E-2;
}

method DotLiteralArithmetic() {
  // Arithmetic with trailing dots
  var a := 5.;         // 5.0
  var b := 2.;         // 2.0
  
  // Arithmetic with leading dots
  var c := .5;         // 0.5
  var d := .25;        // 0.25
  
  // Mixed arithmetic
  assert a + b == 7.0;
  assert a - b == 3.0;
  assert a * b == 10.0;
  assert a / b == 2.5;
  
  assert c + d == 0.75;
  assert c - d == 0.25;
  assert c * d == 0.125;
  assert c / d == 2.0;
  
  // Mixed with traditional forms
  assert a + 1.0 == 6.0;
  assert c * 2.0 == 1.0;
  assert 10. / 2. == 5.0;
  assert .1 + .9 == 1.0;
}

method LargeExponents() {
  // Large positive exponents
  var a := 1.0e10;     // 10,000,000,000.0
  var b := 2.5e8;      // 250,000,000.0
  
  // Large negative exponents
  var c := 1.0e-10;    // 0.0000000001
  var d := 2.5e-8;     // 0.000000025
  
  // Verify relationships
  assert a == 10000000000.0;
  assert b == 250000000.0;
  assert c == 0.0000000001;
  assert d == 0.000000025;
  
  // Mathematical relationships
  assert a / 1.0e10 == 1.0;
  assert b / 1.0e8 == 2.5;
  assert c * 1.0e10 == 1.0;
  assert d * 1.0e8 == 2.5;
}

method ScientificNotationArithmetic() {
  var a := 1.5e2;      // 150.0
  var b := 3.0e1;      // 30.0
  var c := 2.0e-1;     // 0.2
  
  // Basic arithmetic
  assert a + b == 180.0;
  assert a - b == 120.0;
  assert a * c == 30.0;
  assert a / b == 5.0;
  
  // Mixed with regular decimals
  assert a + 50.0 == 200.0;
  assert b * 2.0 == 60.0;
  assert c + 0.8 == 1.0;
}

method EdgeCases() {
  // Zero with scientific notation
  var a := 0.0e5;      // 0.0
  var b := 0e-3;       // 0.0
  
  // Zero with dot literals
  var c := 0.;         // 0.0
  var d := .0;         // 0.0
  
  // Very small numbers
  var e := 1e-100;     // Very small positive
  var f := 1.0e-100;   // Very small positive
  
  // Numbers close to 1
  var g := 9.99e-1;    // 0.999
  var h := 1.01e0;     // 1.01
  
  assert a == b == c == d == 0.0;
  assert e == f > 0.0;
  assert g < 1.0;
  assert h > 1.0;
}

method UnderscoreSupport() {
  // Test underscores in scientific notation for improved readability
  // Dafny already supports underscores in decimal literals (e.g., 1_234.567_890)
  // so we extend this support to scientific notation for consistency
  var a := 1_2.3_4e1_0;    // 123.4e10 - underscores in base and exponent
  var b := 1_0e-0_5;       // 10e-05 = 10e-5 - underscores with negative exponent
  
  // Underscores with dot literals
  var c := 1_000.;         // 1000.0 - trailing dot with underscores
  var d := .1_2_3;         // 0.123 - leading dot with underscores
  
  assert a == 123400000000.0;
  assert b == 0.0001;
  assert c == 1000.0;
  assert d == 0.123;
}

method ComparisonOperations() {
  var small := 1.0e-5;     // 0.00001
  var medium := 1.0e0;     // 1.0
  var large := 1.0e5;      // 100000.0
  
  // Ordering
  assert small < medium;
  assert medium < large;
  assert small < large;
  
  // Equality with equivalent forms
  assert 1.0e2 == 100.0;
  assert 5.0e-1 == 0.5;
  assert 1.0e0 == 1.0;
  
  // Equality with dot literals
  assert 1. == 1.0;
  assert .5 == 0.5;
  assert 5.e1 == 50.0;
  assert .1e1 == 1.0;
}

method TypeConversions() {
  var r := 1.23e2;     // 123.0
  
  // Floor operation
  assert r.Floor == 123;
  
  // Conversion to int (when appropriate)
  assert (1.0e2).Floor == 100;
  assert (5.0e0).Floor == 5;
  
  // Floor with dot literals
  assert (5.).Floor == 5;
  assert (.5e1).Floor == 5;    // 0.5e1 = 5.0
  assert (1.9).Floor == 1;
}
