// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

// ========================================
// Inexact literals without ~ prefix
// ========================================

method TestInexactLiteralsRequireTilde() {
  // Common inexact decimal values
  var bad_d1: fp64 := 0.1;   // Error: literal 0.1 is not exactly representable in fp64, use ~0.1
  var bad_d2: fp64 := 0.2;   // Error: literal 0.2 is not exactly representable in fp64, use ~0.2
  var bad_d3: fp64 := 0.3;   // Error: literal 0.3 is not exactly representable in fp64, use ~0.3
  var bad_d7: fp64 := 0.7;   // Error: literal 0.7 is not exactly representable in fp64, use ~0.7
  var bad_d9: fp64 := 0.9;   // Error: literal 0.9 is not exactly representable in fp64, use ~0.9

  // Mathematical constants
  var bad_pi: fp64 := 3.14159;   // Error: literal 3.14159 is not exactly representable in fp64, use ~3.14159
  var bad_e: fp64 := 2.71828;    // Error: literal 2.71828 is not exactly representable in fp64, use ~2.71828
  var bad_sqrt2: fp64 := 1.41421; // Error: literal 1.41421 is not exactly representable in fp64, use ~1.41421

  // Scientific notation
  var bad_sci1: fp64 := 1.23e-10; // Error: literal 1.23e-10 is not exactly representable in fp64, use ~1.23e-10
  var bad_sci2: fp64 := 3.33e-5;  // Error: literal 3.33e-5 is not exactly representable in fp64, use ~3.33e-5

  // Precision boundaries
  var bad_precise1: fp64 := 1.0000000000000001;   // Error: literal is not exactly representable in fp64
  var bad_precise2: fp64 := 0.9999999999999999;   // Error: literal is not exactly representable in fp64
  var bad_precise3: fp64 := 3.141592653589793238; // Error: literal is not exactly representable in fp64

  // Negative inexact values
  var bad_neg1: fp64 := -0.1;  // Error: literal -0.1 is not exactly representable in fp64, use ~-0.1
  var bad_neg2: fp64 := -0.3;  // Error: literal -0.3 is not exactly representable in fp64, use ~-0.3
  var bad_neg3: fp64 := -3.14; // Error: literal -3.14 is not exactly representable in fp64, use ~-3.14

  // Very high precision literals
  var bad_prec1: fp64 := 0.10000000000000000000000001;  // Error: Not exactly representable
  var bad_prec2: fp64 := 3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679;  // Error: Not exactly representable
  var bad_prec3: fp64 := 1.23456789012345678901234567890e100;  // Error: Not exactly representable
  var bad_prec4: fp64 := 9007199254740992.000000000001;  // Error: Not exactly representable
  var bad_prec5: fp64 := 0.5000000000000000000000001;  // Error: Not exactly representable
}

method TestInexactLiteralsInExpressions() {
  var x: fp64 := 1.0;  // OK: 1.0 is exact

  // Inexact literals in expressions still need the prefix
  var bad_expr1 := x + 0.1;  // Error: literal 0.1 is not exactly representable in fp64, use ~0.1
  var bad_expr2 := x * 0.3;  // Error: literal 0.3 is not exactly representable in fp64, use ~0.3
  var bad_expr3 := x / 0.7;  // Error: literal 0.7 is not exactly representable in fp64, use ~0.7
}

method TestInexactLiteralsAsArguments() {
  // Inexact literals as method arguments need the prefix
  var result := ComputeWithFp64(0.1);  // Error: literal 0.1 is not exactly representable in fp64, use ~0.1
}

method ComputeWithFp64(x: fp64) returns (r: fp64) {
  r := x * 2.0;  // 2.0 is exact, OK
}

method TestInexactLiteralsInArrays() {
  // Inexact literals in array initialization need the prefix
  var arr: array<fp64> := new fp64[3];
  arr[0] := 0.1;  // Error: literal 0.1 is not exactly representable in fp64, use ~0.1
  arr[1] := 0.2;  // Error: literal 0.2 is not exactly representable in fp64, use ~0.2
  arr[2] := 0.3;  // Error: literal 0.3 is not exactly representable in fp64, use ~0.3
}

method Main() {
  // This method should never be reached due to resolver errors
}