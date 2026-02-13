// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

// ========================================
// Invalid ~ prefix usage
// ========================================

method TestTildeNotAllowedOnReal() {
  // ERROR: Using ~ creates an fp64 literal (not fp32), which cannot be assigned to real type
  // The ~ prefix makes these fp64 literals, not real literals
  // Note: Without type suffixes, we cannot force literals to be fp32, so this test doesn't apply to fp32 the same way it does to fp64.
  // var r1: real := ~0.1;   // Error: fp64 literal cannot be assigned to real (type mismatch)
  // var r2: real := ~3.14;  // Error: fp64 literal cannot be assigned to real (type mismatch)
  // var r3: real := ~-0.5;  // Error: fp64 literal cannot be assigned to real (type mismatch) + exact value error
  // var r4: real := ~0.123456789012345678901234567890;  // Error: fp64 literal cannot be assigned to real (type mismatch)
}

method TestNegationWithApproximatePrefix() {
  var a: fp32 := -~0.1;   // Error: The approximate literal prefix ~ cannot be used after unary negation
  var b: fp32 := ~-0.1;   // OK: approximate of -0.1
  var c: fp32 := -(~0.1); // OK: explicit parentheses

  // This is also forbidden in expressions
  var x: fp32 := 1.0;
  var d := x + -~0.1;     // Error: The approximate literal prefix ~ cannot be used after unary negation
  var e := x * -~0.5;     // Error: The approximate literal prefix ~ cannot be used after unary negation
}

method TestTildeOnNonLiterals() {
  // ERROR: ~ prefix should only be allowed on literals, not on expressions or variables

  var x: fp32 := ~0.1;  // OK: ~ on literal
  var y: fp32 := ~0.2;  // OK: ~ on literal

  var bad1: fp32 := ~x;           // Error: ~ not allowed on variables
  var bad2: fp32 := ~(x + y);     // Error: ~ not allowed on expressions
  var bad3: fp32 := ~(0.1 + 0.2); // Error: ~ not allowed on expressions, only literals
}

method TestTildeOnExactLiterals() {
  // ERROR: Using ~ on exactly representable values is forbidden
  // The ~ prefix is only for acknowledging inexact representation

  var bad1: fp32 := ~1.0;   // Error: ~ not allowed; 1.0 is exactly representable in fp32
  var bad2: fp32 := ~0.5;   // Error: ~ not allowed; 0.5 is exactly representable in fp32
  var bad3: fp32 := ~0.25;  // Error: ~ not allowed; 0.25 is exactly representable in fp32
  var bad4: fp32 := ~2.0;   // Error: ~ not allowed; 2.0 is exactly representable in fp32
  var bad5: fp32 := ~4.0;   // Error: ~ not allowed; 4.0 is exactly representable in fp32
  var bad6: fp32 := ~0.125; // Error: ~ not allowed; 0.125 is exactly representable in fp32
}

method TestTildeOnNonFloatingPointTypes() {
  // ERROR: Integer literals should not allow ~ prefix
  var i1: int := ~42;    // Error: ~ prefix not allowed on integer literals
  var i2: int := ~-100;  // Error: ~ prefix not allowed on integer literals
  var i3: int := ~0;     // Error: ~ prefix not allowed on integer literals

  // ERROR: ~ should not be allowed on non-numeric literals
  var c: char := ~'a';        // Error: ~ prefix not allowed on character literals
  var s: string := ~"hello";  // Error: ~ prefix not allowed on string literals
}

method TestTildeTypeInferenceAmbiguity() {
  // Test how ~ affects type inference

  // Without type annotation, Dafny defaults to fp64
  var inferred1 := ~0.1;   // OK: Dafny infers fp64 as the default floating-point type
  var inferred2 := ~3.14;  // OK: Also defaults to fp64

  // With context
  var x: fp32 := 1.0;
  var inferred3 := x + ~0.1;  // OK: type inference from x makes this fp32
}

method Main() {
  // This method should never be reached due to resolver errors
}