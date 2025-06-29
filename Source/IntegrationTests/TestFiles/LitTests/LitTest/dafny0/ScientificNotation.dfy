// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"

// Simple test for scientific notation support

method TestScientificNotation() {
  var a := 1.23e2;     // 123.0
  var b := 5e-1;       // 0.5
  var c := 1.;         // 1.0
  
  assert a == 123.0;
  assert b == 0.5;
  assert c == 1.0;
}
