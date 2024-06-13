// RUN: ! %verify --type-system-refresh --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  x > 0
}

blind method Foo(x: int) 
  requires x > 0
{
  if (*) {
    reveal P;
    assert P(x);
  } else {
    assert P(x); // error
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
