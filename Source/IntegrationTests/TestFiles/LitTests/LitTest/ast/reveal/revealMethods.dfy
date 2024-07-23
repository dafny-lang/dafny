// RUN: ! %verify --type-system-refresh --allow-axioms --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

method MethodEnsuresAreHidden() {
  hide Bar;
  var x := Bar();
  if (*) {
    reveal Bar;
    assert x;
  } else {
    assert x; // error
  }
  assert x;
}

method Bar() returns (x: bool) 
  ensures x