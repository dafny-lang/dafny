// RUN: ! %verify --type-system-refresh --allow-axioms --show-hints --isolate-assertions %s --bprint=%t.bpl > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

method HideAndRevealHappyFlow() {
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

  var y: int := Natty();
  assert y >= 0; // no error
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

module M1 {
    ghost function RecFunc(x: nat): nat { 
        if x == 0 then 0
        else 1 + RecFunc(x - 1)
    }
}
module M2 {
    import opened M1
    lemma Lemma(x: nat) 
    ensures RecFunc(0) == 0
    {
        // Because RecFunc is recursive, it uses the fuel related $LS function, 
        // this was previously hidden by 'hide *', so that the ensures could not be proved
        hide *;
        reveal RecFunc;
    }
}

predicate Outer(x: int) {
  Inner(x)
}

predicate Inner(x: int) {
  x > 3
}

method InnerOuterUser() {
  hide *;
  assert Outer(0);
  assert Outer(1) by {
    reveal Outer;
  }
  assert Outer(2) by {
    reveal Inner;
  }
  assert Outer(3) by {
    reveal Outer, Inner;
  }
}

  
function HideInFunction(): int 
  ensures true
{
  var x := 3; // Trigger substitute logic 
  assert P(0) by {
    hide *;
  }
  hide *;
  assert P(1);
  reveal P;
  assert P(2);
  3
}
 