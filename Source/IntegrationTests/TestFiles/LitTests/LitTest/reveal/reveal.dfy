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
    assert EnsuresFuncFoo(); // error
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

blind method RevealExpressionScope()
{
  reveal P;
  reveal Q;
  assert Q() == 3;
  assert reveal P; reveal Q; Q() == 3;
  assert P();
}

blind method MethodEnsuresAreHidden() {
  // var x := Bar();
  // if (*) {
  //   reveal Bar();
  //   assert x;
  // } else {
  //   assert x; // error
  // }
  // assert x;
}

method Bar() returns (x: bool) 
  ensures x


// Consequence axiom also contains information about subset types of the return types
// Reveals in contracts are fine, but they never escape the contract.

// Add an option 
// TODO what to do with reveals in contracts?
// TODO add test cases that see how blindness interops with contracts of the blind callable
// TODO if a contract has reveals clauses, do they get copied to the caller?