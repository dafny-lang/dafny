// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

// Comprehensive test for scientific notation and trailing dot support

method BasicScientificNotation() {
  // Basic positive exponents
  var a := 1.23e2;     // 123.0
  var b := 1.23e2;     // 123.0 (only lowercase e supported)
  var c := 1.23e2;     // 123.0 (no explicit + needed)
  
  // Basic negative exponents  
  var d := 1.23e-2;    // 0.0123
  var e := 1.23e-2;    // 0.0123 (only lowercase e supported)
  
  // Zero exponent
  var f := 1.23e0;     // 1.23
  var g := 1.23e0;     // 1.23 (no + needed)
  var h := 1.23e-0;    // 1.23
  
  // Verify basic equivalences
  assert a == b && b == c && c == 123.0;
  assert d == e && e == 0.0123;
  assert f == g && g == h && h == 1.23;
}

method IntegerScientificNotation() {
  // Integer base with scientific notation
  var a := 5e2;        // 500.0
  var b := 5e2;        // 500.0 (only lowercase e)
  var c := 5e2;        // 500.0 (no + needed)
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

method TrailingDotWithScientificNotation() {
  // Trailing dot combined with scientific notation
  var a := 1.e2;       // 100.0
  var b := 5.e-1;      // 0.5 (only lowercase e)
  var c := 2.e3;       // 2000.0 (no + needed)
  
  // With underscores
  var d := 1_000.e2;   // 100000.0
  
  // Verify values
  assert a == 100.0;
  assert b == 0.5;
  assert c == 2000.0;
  assert d == 100000.0;
}

method TupleAccessCompatibility() {
  // Verify that tuple member access still works (no conflict)
  var tuple := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
  var first := tuple.0;
  var fifth := tuple.5;
  var tenth := tuple.10;
  var fifteenth := tuple.14;
  
  assert first == 1;
  assert fifth == 6;
  assert tenth == 11;
  assert fifteenth == 15;
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
}

method UnderscoreSupport() {
  // Scientific notation with underscores
  var a := 1_234.567_8e2;    // 123456.78
  var b := 5_000e-3;         // 5.0
  var c := 1_000.e1;         // 10000.0
  
  // Verify values
  assert a == 123456.78;
  assert b == 5.0;
  assert c == 10000.0;
}

method EdgeCases() {
  // Very small and very large numbers
  var small := 1.0e-10;     // 0.0000000001
  var large := 1.0e10;      // 10000000000.0
  
  // Zero with scientific notation
  var zero1 := 0.0e5;       // 0.0
  var zero2 := 0.e-3;       // 0.0
  
  assert small == 0.0000000001;
  assert large == 10000000000.0;
  assert zero1 == 0.0;
  assert zero2 == 0.0;
}
