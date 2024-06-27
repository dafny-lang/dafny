// echo ''
// NoRUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// NoRUN: %diff "%s.expect" "%t"

blind method MethodEnsuresAreHidden() {
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