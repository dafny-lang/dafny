// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

method MatchStatementScope(x: int) {
  hide *;
  match x {
    case 0 =>
      reveal P;
      assert P(0);
    case _ =>
      assert P(1); // error
  }
  assert P(2); // error
}