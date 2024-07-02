// echo ''
// NORUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// NORUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

function Q(): int 
  requires P(0) {
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
  hide *;
  {
    reveal P;
    assert P(0);
  }
  assert P(1); // error
}

method Forall() {
  hide *;
  var aa := new int[3];
  forall i | 0 <= i < aa.Length
  {
    aa[i] := 0;
    // Somehow the next two lines cause the entire forall to become a ghost context
    // reveal P;
    // assert P(0);
  }
  assert P(1); // error
}

method While() {
  hide *;
  var x := 3;
  while(x > 0) {
    reveal P;
    assert P(0);
    x := x - 1;
  }
  assert P(1); // error
}

// Calc statement

// If-alternative statement. Does anyone use that?