// RUN: %testDafnyForEachResolver "%s" -- --print:-


// Test that the `IsTypeSequence` method of the parser allows tuples with ghost components.
function F(x: int): () { () }
function a<T,U>(x: int): int { x }
method M<b, c>(d: int) {
  var u;
  u := F( a < (b, ghost b), c > (d) );
  u := F( a < (b, (ghost b, ghost b)), c > (d) );
  u := F( a < (b, ((ghost b, b), ghost b)), c > (d) );
}
