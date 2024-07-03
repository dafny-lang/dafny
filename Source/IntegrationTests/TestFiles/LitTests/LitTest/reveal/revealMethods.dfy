// RUN: echo ''
// No: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// No: %diff "%s.expect" "%t"

method MethodEnsuresAreHidden() {
  hide *;
  var x := Bar();
  if (*) {
    reveal Bar();
    assert x;
  } else {
    assert x; // error
  }
  assert x;
}

method Bar() returns (x: bool) 
  ensures x