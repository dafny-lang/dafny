// echo ''
// NoRUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// NoRUN: %diff "%s.expect" "%t"

function P(): bool {
  true
}

function Q(): int 
  requires P() {
  3
}

blind method FunctionSubsetResult(a: nat) {
  assert a >= 0;
  if (*) { 
    var x: nat := Natty();
    assert x >= 0;
  } else if (*) {
    var y: int := Natty();
    assert y >= 0;
  } else {
    reveal Natty;
    var z: nat := Natty();
    assert z >= 0;
  }
}
function Natty(): nat {
  3
}