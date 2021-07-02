// RUN: %dafny /compile:0 /dprint:- "%s" /env:0 > "%t"
// RUN: %diff "%s.expect" "%t"

// Test that the `IsTypeSequence` method of the parser allows tuples with ghost components.
module M1 {
  class C1 {
    function method F(x: int): () { () }
    function method a<T,U>(x: int): int { x }
    method M<b, c>(d: int) {
      var u;
      u := F( a < (b, ghost b), c > (d) );
      u := F( a < (b, (ghost b, ghost b)), c > (d) );
      u := F( a < (b, ((ghost b, b), ghost b)), c > (d) );
    }
  }
}
