// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

blind method FunctionSubsetResult() {
  if (*) { 
    reveal Natty;
    var x: nat := Natty();
    assert x >= 0; // no error
  } else if (*) {
    var y: nat := Natty();
    assert y >= 0; // right now error, 
    // would be nice if it passes based on the type of y
    // if nat is revealed
  } else {
    var z: int := Natty();
    assert z >= 0; // error
  }
}
function Natty(): nat