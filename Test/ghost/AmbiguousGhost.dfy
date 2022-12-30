// RUN: %baredafny verify %args --print=- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test that the `IsTypeSequence` method of the parser allows tuples with ghost components.
function method F(x: int): () { () }
function method a<T,U>(x: int): int { x }
method M<b, c>(d: int) {
  var u;
  u := F( a < (b, ghost b), c > (d) );
  u := F( a < (b, (ghost b, ghost b)), c > (d) );
  u := F( a < (b, ((ghost b, b), ghost b)), c > (d) );
}
