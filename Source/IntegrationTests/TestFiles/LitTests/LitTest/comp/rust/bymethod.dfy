// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


abstract module ReverseHolder {
  newtype U8 = x: int | 0 <= x < 256
  type U8Seq = seq<U8>
  type WellFormedSequence = s: U8Seq | |s| == 0 || |s| != 0 witness []

  function Reverse(vs: seq<U8>): (s: WellFormedSequence) {
    if |vs| == 0 then [] else
    Reverse(vs[1..]) + [vs[0]]
  } by method {
    s := [];
    assert vs == vs[0..|vs|];
    for i := |vs| downto 0
      invariant s == Reverse(vs[i..])
    {
      s := s + [vs[i]];
    }
  }
}
module Reverser refines ReverseHolder {
}

method Main() {
  expect Reverser.Reverse([1, 2]) == [2, 1];
  print "Everything ok";
}