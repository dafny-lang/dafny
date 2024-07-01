// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

method HideAndRevealStatementScoping() {
  hide *;
  
  if (*) {
    reveal P;
    assert P(0);
  } else {
    assert P(0); // error
  }
  reveal P;
  if (*) {
    assert P(1);
  } else {
    hide *;
    assert P(1); // error
  }
  
  hide *;
  if (*) {
    reveal P;
  } else {
    reveal P;
  }
  assert P(2); // error, since the previous two reveal statements are out of scope
}

function EnsuresFuncFoo(): bool
  ensures EnsuresFuncFoo()

method UseEnsuresFuncFoo() {
  hide *;
  if (*) {
    reveal EnsuresFuncFoo;
    assert EnsuresFuncFoo();
  } else {
    assert EnsuresFuncFoo(); // no error. Could be changed in the future
  }
}

opaque predicate OpaqueFunc() {
  true
}

method OpaqueUser() {
  hide *;
  if (*) {
    reveal OpaqueFunc;
    assert OpaqueFunc();
  } else {
    assert OpaqueFunc(); // error
  }
}

// Subset results
method FunctionSubsetResult() {
  hide *;
  var x: nat := Natty();
  assert x >= 0; // no error
}

function Natty(): nat {
  3
}

// Reads clause
class O { var x: int }
function Obj(o: O): int 
  ensures Obj(o) > 0
{
  3
}

method ReadsClause() {
  hide *;
  var o := new O;
  var before := Obj(o);
  o.x := 3;
  if (*) {
    assert Obj(o) == before; // passes, because at the moment reads clauses are never hidden
  } else {
    assert Obj(o) == before by { // passes
      reveal Obj;
    }
  }
}