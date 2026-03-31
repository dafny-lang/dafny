// RUN: %verify --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: assigned() crashed with --relax-definite-assignment
// because the definite assignment tracker was not set up.

method M() {
  var x := 3;
  assert assigned(x);
}
