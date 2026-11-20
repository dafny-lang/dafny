// RUN: %verify "%s" > "%t"
// RUN: %verify --relax-definite-assignment "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Regression test: assigned() crashed whenever the variable had no definite-assignment
// tracker. That is not specific to --relax-definite-assignment: NeedsDefiniteAssignmentTracker
// declines to create one for an auto-initializable local at every level, and in-parameters are
// never in the table at all, so the default configuration crashed too. Both are run here.

method LocalWithInitializer() {
  var x := 3;
  assert assigned(x);
}

method LocalWithoutInitializer() {
  var x: int;
  x := 3;
  assert assigned(x);
}

method InParameter(a: int) {
  assert assigned(a);
}

method OutParameter() returns (y: int) {
  y := 1;
  assert assigned(y);
}

class C {
  var f: int
  constructor () {
    f := 3;
    assert assigned(f);
  }
}
