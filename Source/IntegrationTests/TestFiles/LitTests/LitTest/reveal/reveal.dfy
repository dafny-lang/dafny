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

// TODO add test cases that see how blindness interops with contracts of the blind callable
// TODO if a contract has reveals clauses, do they get copied to the caller?