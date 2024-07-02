// echo ''
// NORUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// NORUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

function Q(): int 
  requires P() {
  3
}

method IfScope() {
  hide *;
  if (*) {
    reveal P;
  } else {
    reveal P;
  }
  assert P(2); // error, since the previous two reveal statements are out of scope
}

method MatchStatementScope(x: int) {
  hide *;
  match x {
    case 0 =>
      reveal P;
      assert P(0);
    case _ =>
      assert P(0); // error
  }
  assert P(1); // error
}

method BlockScope() {
  {
    reveal P;
    assert P(0);
  }
  assert P(1); // error
}

method Forall(a: Array<int>) {
  forall i | 0 <= i < a.Length {
    a[i] := 0;
    reveal P;
    assert P(0);
  }
  assert P(1); // error
}

method While() {
  var x := 3;
  while(x > 0) {
    reveal P;
    assert P(0);
    x := x - 1;
  }
  assert P(1); // error
}