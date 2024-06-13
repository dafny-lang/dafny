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