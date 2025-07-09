// NONUNIFORM: Testing explicit newtype conversion of bounded ranges in Rust backend
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint8  = x: int | 0 <= x < 0x100
newtype uint16 = x: int | 0 <= x < 0x10000

function UInt16ToSeq(x: uint16): seq<uint8> {
  var b0 := (x / 0x100) as uint8;
  var b1 := (x % 0x100) as uint8;
  [b0, b1]
}

method Main() {
  var a := set x: uint16 | 0 <= x < 0xFFFF :: UInt16ToSeq(x);
}