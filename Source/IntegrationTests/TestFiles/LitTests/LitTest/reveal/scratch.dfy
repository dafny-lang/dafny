// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

method BlockScope() {
  {
    reveal P;
    assert P(0);
  }
  assert P(1); // error
}