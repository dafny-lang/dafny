// RUN: ! %verify --type-system-refresh --allow-axioms --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

function P(): nat

method Foo(x: nat) {
  hide nat;
  if (*) {
    assert x > 0; // Fails because nat is hidden
  } else {
    reveal nat;
    assert x > 0; // No error
  }
  var y := P();
  assert y > 0; // Fails because nat is hidden, even though P is revealed
  
  var z: int := P();
  reveal nat;
  assert z > 0; // Fails because z is an int
  
  hide P;
  var a: nat := P();
  assert a > 0; // Passes, because nat is revealed, even though P is hidden.
  
  var b: nat := *;
  assert b >= 0; // Passes
  
  var c: int := *;
  if (*) {
    assert c > 0; // Fails
  }
  var d: nat := c by { // New syntax
    assume c >= 0;
  }
  assert d > 0; // Passes
}