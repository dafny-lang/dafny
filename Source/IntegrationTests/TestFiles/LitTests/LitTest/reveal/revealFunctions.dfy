// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function P(): bool {
  true
}

blind method Foo()
{
  if (*) {
    reveal P;
    assert P();
  } else {
    assert P(); // error
  }
}

blind function Zer(): int {
  Q() // requires error
}

blind function Zaz(): int {
  reveal P; 
  Q()
}

function Q(): int 
  requires P() {
  3
}

function EnsuresFuncFoo(): bool
  ensures EnsuresFuncFoo()

blind method UseEnsuresFuncFoo() {
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

blind method OpaqueUser() {
  if (*) {
    reveal OpaqueFunc;
    assert OpaqueFunc();
  } else {
    assert OpaqueFunc(); // error
  }
}

blind method FunctionSubsetResult() {
    var x: nat := Natty();
    assert x >= 0; // no error
}

function Natty(): nat {
  3
}
class O { var x: int }
function Obj(o: O): int 
  ensures Obj(o) > 0
{
  3
}

blind method ReadsClause() {
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