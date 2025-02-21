// NONUNIFORM: Testing robustness of Dafny/Rust backends wrt set comprehension
// RUN: %baredafny build --function-syntax:3 --target:rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Spoo {
  newtype uint8 = x: int | 0 <= x < 0x100
  newtype uint16 = x: int | 0 <= x < 0x10000
  function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
    ensures |ret| == 2
    ensures 0x100 * ret[0] as uint16 + ret[1] as uint16 == x
  {
    var b0 := (x / 0x100) as uint8;
    var b1 := (x % 0x100) as uint8;
    [b0, b1]
  }

  method {:test} TestSetToOrderedSequenceManyItems() {
    var a := set x:uint16 | 0 <= x < 0xFFFF :: UInt16ToSeq(x);
  }
}