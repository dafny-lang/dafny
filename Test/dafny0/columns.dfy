// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Dafny counts columns from 0, but Boogie from one, so for a while there were small bugs with that.

predicate P(x: int)

static method A(x:int) requires x > 0 { // error os 's'
  assert (forall y: int :: P(y)); // error on '('
  assert x != 1; // error on '!'
  assert x in {}; // error on 'i'
}
