// echo ''
// NORUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// NORUN: %diff "%s.expect" "%t"

function P(): bool {
  true
}

function Q(): int 
  requires P() {
  3
}

blind method RevealExpressionScope()
{
  reveal P;
  reveal Q;
  assert Q() == 3;
  assert reveal P; reveal Q; Q() == 3;
  assert P();
}