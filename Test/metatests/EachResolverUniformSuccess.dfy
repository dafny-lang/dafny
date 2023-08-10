// RUN: %testDafnyForEachResolver "%s"

// This little program type checks and verifies with both the legacy resolver and the refresh resolver.

// This is a Main method, but the compiler is not run as part of this test. Hence, the meta-test also tests
// that the compiler is not run.

method Main() {
  var x: nat := 17;
  var y := x;
  for i := 0 to 3 {
    y := x;
  }
  print y, "\n";
}
