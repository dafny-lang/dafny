// RUN: %testDafnyForEachCompiler "%s"

const TWO_TO_THE_8: int := 0x100
newtype uint8 = x: int | 0 <= x < TWO_TO_THE_8

method Main() {
  var i: uint8 := 10;
  var s: seq<uint8> := seq(i, _ => 0);
  print s;
}